/*
 * Copyright (c) 2001, 2010, Oracle and/or its affiliates. All rights reserved.
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

#include "jni.h"
#include "jni_util.h"
#include "jvm.h"
#include "jlong.h"
#include "java_nio_MappedByteBuffer.h"
#include <sys/mman.h>
#include <stddef.h>
#include <stdlib.h>

JNIEXPORT jboolean JNICALL
Java_java_nio_MappedByteBuffer_isLoaded0(JNIEnv *env, jobject obj, jlong address,
                                         jlong len, jint numPages)
{
    jboolean loaded = JNI_TRUE;
    int result = 0;
    int i = 0;
    void *a = (void *) jlong_to_ptr(address);
#ifdef __linux__
    unsigned char *vec = (unsigned char *)malloc(numPages * sizeof(char)); // 分配内存
#else
    char *vec = (char *)malloc(numPages * sizeof(char));
#endif

    if (vec == NULL) {
        JNU_ThrowOutOfMemoryError(env, NULL);
        return JNI_FALSE;
    }

    result = mincore(a, (size_t)len, vec); // 用来确定一个给定范围的内存是在物理内存中还是被交换到了硬盘中
    if (result == -1) {
        JNU_ThrowIOExceptionWithLastError(env, "mincore failed");
        free(vec);
        return JNI_FALSE;
    }

    for (i=0; i<numPages; i++) { // vec的每个字节对应指定区域内的一个页面，第一个字节对应着第一个页面，然后依次对应
        if (vec[i] == 0) {  // 如果页面在物理内存中，对应字节的最低位是1,否则是0
            loaded = JNI_FALSE;
            break;
        }
    }
    free(vec); // 释放vec的内存
    return loaded;
}


JNIEXPORT void JNICALL
Java_java_nio_MappedByteBuffer_load0(JNIEnv *env, jobject obj, jlong address,
                                     jlong len)
{
    char *a = (char *)jlong_to_ptr(address);
    int result = madvise((caddr_t)a, (size_t)len, MADV_WILLNEED); // 给操作系统建议，说这文件在不久的将来要访问的，因此，提前读几页可能是个好主意
    if (result == -1) {
        JNU_ThrowIOExceptionWithLastError(env, "madvise failed");
    }
}


JNIEXPORT void JNICALL
Java_java_nio_MappedByteBuffer_force0(JNIEnv *env, jobject obj, jobject fdo,
                                      jlong address, jlong len)
{
    void* a = (void *)jlong_to_ptr(address);
    int result = msync(a, (size_t)len, MS_SYNC); // 内容写回磁盘  调用会等到更新完成之后返回
    if (result == -1) {
        JNU_ThrowIOExceptionWithLastError(env, "msync failed");
    }
}
