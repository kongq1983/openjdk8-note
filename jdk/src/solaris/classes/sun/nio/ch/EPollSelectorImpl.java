/*
 * Copyright (c) 2005, 2013, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package sun.nio.ch;

import java.io.IOException;
import java.nio.channels.*;
import java.nio.channels.spi.*;
import java.util.*;
import sun.misc.*;

/**
 * An implementation of Selector for Linux 2.6+ kernels that uses
 * the epoll event notification facility.
 */
class EPollSelectorImpl
    extends SelectorImpl
{

    // File descriptors used for interrupt
    protected int fd0; // 管道的读端文件描述符
    protected int fd1; //管道的写端文件描述符

    // The poll object 调用底层Epoll算法的包装类
    EPollArrayWrapper pollWrapper;

    // Maps from file descriptors to keys 保存文件描述符句柄和的SelectionKey的映射关系
    private Map<Integer,SelectionKeyImpl> fdToKey;

    // True if this Selector has been closed
    private volatile boolean closed = false;

    // Lock for interrupt triggering and clearing
    private final Object interruptLock = new Object();
    private boolean interruptTriggered = false;

    /**
     * Package private constructor called by factory method in
     * the abstract superclass Selector.
     */
    EPollSelectorImpl(SelectorProvider sp) throws IOException {
        super(sp);
        long pipeFds = IOUtil.makePipe(false); // Native调用pipe()函数返回两个文件描述符
        fd0 = (int) (pipeFds >>> 32); // 无符号移位  管道的读端文件描述符
        fd1 = (int) pipeFds;  //管道的写端文件描述符
        pollWrapper = new EPollArrayWrapper(); //调用底层Epoll算法的包装类
        pollWrapper.initInterrupt(fd0, fd1);
        fdToKey = new HashMap<>();
    }
    // todo doSelect
    protected int doSelect(long timeout) throws IOException { // select(0)=-1   selectNow():0
        if (closed)
            throw new ClosedSelectorException(); // 已关闭，抛出异常
        processDeregisterQueue(); // 处理取消的集合
        try {
            begin();
            pollWrapper.poll(timeout);
        } finally {
            end();
        }
        processDeregisterQueue();
        int numKeysUpdated = updateSelectedKeys();
        if (pollWrapper.interrupted()) {
            // Clear the wakeup pipe
            pollWrapper.putEventOps(pollWrapper.interruptedIndex(), 0);
            synchronized (interruptLock) {
                pollWrapper.clearInterrupted();
                IOUtil.drain(fd0);
                interruptTriggered = false;
            }
        }
        return numKeysUpdated;
    }

    /**
     * Update the keys whose fd's have been selected by the epoll.
     * Add the ready keys to the ready queue.
     */
    private int updateSelectedKeys() {
        int entries = pollWrapper.updated;
        int numKeysUpdated = 0;
        for (int i=0; i<entries; i++) {  // 从0开始
            int nextFD = pollWrapper.getDescriptor(i); // 获取FD
            SelectionKeyImpl ski = fdToKey.get(Integer.valueOf(nextFD)); // 根据FD找到对应的SelectionKey
            // ski is null in the case of an interrupt
            if (ski != null) {  // 找到该FD的READY事件
                int rOps = pollWrapper.getEventOps(i);
                if (selectedKeys.contains(ski)) { //如果selectedKeys中已经存在这个SelectionKey,则说明是代码出现了读取完socketChannel的数据之后没有调用其close()导致的,调用channel.close(),就会在processDeregisterQueue()中将该selectionKey从selectedKeys中移除
                    if (ski.channel.translateAndSetReadyOps(rOps, ski)) { // 也就是有没有注册的事件返回  将底层的事件转换为Java封装的事件,SelectionKey.OP_READ等
                        numKeysUpdated++;
                    }
                } else {
                    ski.channel.translateAndSetReadyOps(rOps, ski); //也就是有没有注册的事件返回  转换epoll的events到channel定义的events
                    if ((ski.nioReadyOps() & ski.nioInterestOps()) != 0) {
                        selectedKeys.add(ski); //往成员selectedKeys中添加SelectionKey,在这之后调用selector.selectedKeys()就会返回这个成员
                        numKeysUpdated++;
                    }
                }
            }
        }
        return numKeysUpdated; // 返回Ready的Channel个数
    }

    protected void implClose() throws IOException {
        if (closed)
            return;
        closed = true;

        // prevent further wakeup
        synchronized (interruptLock) {
            interruptTriggered = true;
        }

        FileDispatcherImpl.closeIntFD(fd0);
        FileDispatcherImpl.closeIntFD(fd1);

        pollWrapper.closeEPollFD();
        // it is possible
        selectedKeys = null;

        // Deregister channels
        Iterator<SelectionKey> i = keys.iterator();
        while (i.hasNext()) {
            SelectionKeyImpl ski = (SelectionKeyImpl)i.next();
            deregister(ski);
            SelectableChannel selch = ski.channel();
            if (!selch.isOpen() && !selch.isRegistered())
                ((SelChImpl)selch).kill();
            i.remove();
        }

        fd0 = -1;
        fd1 = -1;
    }

    protected void implRegister(SelectionKeyImpl ski) { // ski.selector = SelectorImpl selector
        if (closed) // channel.channel = ServerSocketChannel or SocketChannel
            throw new ClosedSelectorException();
        SelChImpl ch = ski.channel; // ServerSocketChannel or SocketChannel
        int fd = Integer.valueOf(ch.getFDVal()); // 文件描述符
        fdToKey.put(fd, ski); // 把linux的fd和java的SelectionKeyImpl绑定
        pollWrapper.add(fd);  // 添加到pollWrapper
        keys.add(ski);  // java的keys队列添加SelectionKeyImpl
    }

    protected void implDereg(SelectionKeyImpl ski) throws IOException {
        assert (ski.getIndex() >= 0);
        SelChImpl ch = ski.channel; // 得到channel
        int fd = ch.getFDVal(); // 得到fd
        fdToKey.remove(Integer.valueOf(fd)); // 从map删除文件描述符和的SelectionKey的映射关系
        pollWrapper.remove(fd); // EPOLL_CTL_DEL remove from epoll
        ski.setIndex(-1);
        keys.remove(ski); //从注册的Selector删除本SelectionKey
        selectedKeys.remove(ski); // 从已就绪的事件列表中删除本SelectionKey
        deregister((AbstractSelectionKey)ski);  // AbstractSelector.deregister调用 最终((AbstractSelectableChannel)key.channel()).removeKey(key) 从Channel删除该SelectionKey
        SelectableChannel selch = ski.channel();
        if (!selch.isOpen() && !selch.isRegistered())
            ((SelChImpl)selch).kill();
    }

    public void putEventOps(SelectionKeyImpl ski, int ops) {
        if (closed)
            throw new ClosedSelectorException();
        SelChImpl ch = ski.channel;
        pollWrapper.setInterest(ch.getFDVal(), ops);
    }

    public Selector wakeup() {
        synchronized (interruptLock) {
            if (!interruptTriggered) {
                pollWrapper.interrupt();
                interruptTriggered = true;
            }
        }
        return this;
    }
}
