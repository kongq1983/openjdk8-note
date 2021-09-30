/*
 * Copyright (c) 2010, 2013, Oracle and/or its affiliates. All rights reserved.
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

package jdk.nashorn.internal.runtime.linker;

import static jdk.nashorn.internal.codegen.CompilerConstants.staticCallNoLookup;
import static jdk.nashorn.internal.runtime.ECMAErrors.typeError;

import java.lang.invoke.CallSite;
import java.lang.invoke.ConstantCallSite;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodHandles.Lookup;
import java.lang.invoke.MethodType;
import jdk.internal.dynalink.CallSiteDescriptor;
import jdk.internal.dynalink.DynamicLinker;
import jdk.internal.dynalink.DynamicLinkerFactory;
import jdk.internal.dynalink.GuardedInvocationFilter;
import jdk.internal.dynalink.beans.BeansLinker;
import jdk.internal.dynalink.beans.StaticClass;
import jdk.internal.dynalink.linker.GuardedInvocation;
import jdk.internal.dynalink.linker.LinkRequest;
import jdk.internal.dynalink.linker.LinkerServices;
import jdk.internal.dynalink.linker.MethodTypeConversionStrategy;
import jdk.internal.dynalink.support.TypeUtilities;
import jdk.nashorn.api.scripting.JSObject;
import jdk.nashorn.internal.codegen.CompilerConstants.Call;
import jdk.nashorn.internal.codegen.ObjectClassGenerator;
import jdk.nashorn.internal.codegen.RuntimeCallSite;
import jdk.nashorn.internal.lookup.MethodHandleFactory;
import jdk.nashorn.internal.lookup.MethodHandleFunctionality;
import jdk.nashorn.internal.objects.ScriptFunctionImpl;
import jdk.nashorn.internal.runtime.ECMAException;
import jdk.nashorn.internal.runtime.JSType;
import jdk.nashorn.internal.runtime.OptimisticReturnFilters;
import jdk.nashorn.internal.runtime.ScriptFunction;
import jdk.nashorn.internal.runtime.ScriptRuntime;
import jdk.nashorn.internal.runtime.options.Options;

/**
 * This class houses bootstrap method for invokedynamic instructions generated by compiler.
 */
public final class Bootstrap {
    /** Reference to the seed boostrap function */
    public static final Call BOOTSTRAP = staticCallNoLookup(Bootstrap.class, "bootstrap", CallSite.class, Lookup.class, String.class, MethodType.class, int.class);

    private static final MethodHandleFunctionality MH = MethodHandleFactory.getFunctionality();

    private static final MethodHandle VOID_TO_OBJECT = MH.constant(Object.class, ScriptRuntime.UNDEFINED);

    /**
     * The default dynalink relink threshold for megamorphisism is 8. In the case
     * of object fields only, it is fine. However, with dual fields, in order to get
     * performance on benchmarks with a lot of object instantiation and then field
     * reassignment, it can take slightly more relinks to become stable with type
     * changes swapping out an entire proprety map and making a map guard fail.
     * Therefore the relink threshold is set to 16 for dual fields (now the default).
     * This doesn't seem to have any other negative performance implication.
     *
     * See for example octane.gbemu, run with --log=fields:warning to study
     * megamorphic behavior
     */
    private static final int NASHORN_DEFAULT_UNSTABLE_RELINK_THRESHOLD =
            ObjectClassGenerator.OBJECT_FIELDS_ONLY ?
                     8 :
                    16;

    // do not create me!!
    private Bootstrap() {
    }

    private static final DynamicLinker dynamicLinker;
    static {
        final DynamicLinkerFactory factory = new DynamicLinkerFactory();
        final NashornBeansLinker nashornBeansLinker = new NashornBeansLinker();
        factory.setPrioritizedLinkers(
            new NashornLinker(),
            new NashornPrimitiveLinker(),
            new NashornStaticClassLinker(),
            new BoundCallableLinker(),
            new JavaSuperAdapterLinker(),
            new JSObjectLinker(nashornBeansLinker),
            new BrowserJSObjectLinker(nashornBeansLinker),
            new ReflectionCheckLinker());
        factory.setFallbackLinkers(nashornBeansLinker, new NashornBottomLinker());
        factory.setSyncOnRelink(true);
        factory.setPrelinkFilter(new GuardedInvocationFilter() {
            @Override
            public GuardedInvocation filter(final GuardedInvocation inv, final LinkRequest request, final LinkerServices linkerServices) {
                final CallSiteDescriptor desc = request.getCallSiteDescriptor();
                return OptimisticReturnFilters.filterOptimisticReturnValue(inv, desc).asType(linkerServices, desc.getMethodType());
            }
        });
        factory.setAutoConversionStrategy(new MethodTypeConversionStrategy() {
            @Override
            public MethodHandle asType(final MethodHandle target, final MethodType newType) {
                return unboxReturnType(target, newType);
            }
        });
        final int relinkThreshold = Options.getIntProperty("nashorn.unstable.relink.threshold", NASHORN_DEFAULT_UNSTABLE_RELINK_THRESHOLD);
        if (relinkThreshold > -1) {
            factory.setUnstableRelinkThreshold(relinkThreshold);
        }

        // Linkers for any additional language runtimes deployed alongside Nashorn will be picked up by the factory.
        factory.setClassLoader(Bootstrap.class.getClassLoader());

        dynamicLinker = factory.createLinker();
    }

    /**
     * Returns if the given object is a "callable"
     * @param obj object to be checked for callability
     * @return true if the obj is callable
     */
    public static boolean isCallable(final Object obj) {
        if (obj == ScriptRuntime.UNDEFINED || obj == null) {
            return false;
        }

        return obj instanceof ScriptFunction ||
            isJSObjectFunction(obj) ||
            BeansLinker.isDynamicMethod(obj) ||
            obj instanceof BoundCallable ||
            isFunctionalInterfaceObject(obj) ||
            obj instanceof StaticClass;
    }

    /**
     * Returns true if the given object is a strict callable
     * @param callable the callable object to be checked for strictness
     * @return true if the obj is a strict callable, false if it is a non-strict callable.
     * @throws ECMAException with {@code TypeError} if the object is not a callable.
     */
    public static boolean isStrictCallable(final Object callable) {
        if (callable instanceof ScriptFunction) {
            return ((ScriptFunction)callable).isStrict();
        } else if (isJSObjectFunction(callable)) {
            return ((JSObject)callable).isStrictFunction();
        } else if (callable instanceof BoundCallable) {
            return isStrictCallable(((BoundCallable)callable).getCallable());
        } else if (BeansLinker.isDynamicMethod(callable) || callable instanceof StaticClass) {
            return false;
        }
        throw notFunction(callable);
    }

    private static ECMAException notFunction(final Object obj) {
        return typeError("not.a.function", ScriptRuntime.safeToString(obj));
    }

    private static boolean isJSObjectFunction(final Object obj) {
        return obj instanceof JSObject && ((JSObject)obj).isFunction();
    }

    /**
     * Returns if the given object is a dynalink Dynamic method
     * @param obj object to be checked
     * @return true if the obj is a dynamic method
     */
    public static boolean isDynamicMethod(final Object obj) {
        return BeansLinker.isDynamicMethod(obj instanceof BoundCallable ? ((BoundCallable)obj).getCallable() : obj);
    }

    /**
     * Returns if the given object is an instance of an interface annotated with
     * java.lang.FunctionalInterface
     * @param obj object to be checked
     * @return true if the obj is an instance of @FunctionalInterface interface
     */
    public static boolean isFunctionalInterfaceObject(final Object obj) {
        return !JSType.isPrimitive(obj) && (NashornBeansLinker.getFunctionalInterfaceMethod(obj.getClass()) != null);
    }

    /**
     * Create a call site and link it for Nashorn. This version of the method conforms to the invokedynamic bootstrap
     * method expected signature and is referenced from Nashorn generated bytecode as the bootstrap method for all
     * invokedynamic instructions.
     * @param lookup MethodHandle lookup. Ignored as Nashorn only uses public lookup.
     * @param opDesc Dynalink dynamic operation descriptor.
     * @param type   Method type.
     * @param flags  flags for call type, trace/profile etc.
     * @return CallSite with MethodHandle to appropriate method or null if not found.
     */
    public static CallSite bootstrap(final Lookup lookup, final String opDesc, final MethodType type, final int flags) {
        return dynamicLinker.link(LinkerCallSite.newLinkerCallSite(lookup, opDesc, type, flags));
    }

    /**
     * Bootstrapper for a specialized Runtime call
     *
     * @param lookup       lookup
     * @param initialName  initial name for callsite
     * @param type         method type for call site
     *
     * @return callsite for a runtime node
     */
    public static CallSite runtimeBootstrap(final MethodHandles.Lookup lookup, final String initialName, final MethodType type) {
        return new RuntimeCallSite(type, initialName);
    }

    /**
     * Boostrapper for math calls that may overflow
     * @param lookup         lookup
     * @param name           name of operation
     * @param type           method type
     * @param programPoint   program point to bind to callsite
     *
     * @return callsite for a math instrinic node
     */
    public static CallSite mathBootstrap(final MethodHandles.Lookup lookup, final String name, final MethodType type, final int programPoint) {
        final MethodHandle mh;
        switch (name) {
        case "iadd":
            mh = JSType.ADD_EXACT.methodHandle();
            break;
        case "isub":
            mh = JSType.SUB_EXACT.methodHandle();
            break;
        case "imul":
            mh = JSType.MUL_EXACT.methodHandle();
            break;
        case "idiv":
            mh = JSType.DIV_EXACT.methodHandle();
            break;
        case "irem":
            mh = JSType.REM_EXACT.methodHandle();
            break;
        case "ineg":
            mh = JSType.NEGATE_EXACT.methodHandle();
            break;
        case "ladd":
            mh = JSType.ADD_EXACT_LONG.methodHandle();
            break;
        case "lsub":
            mh = JSType.SUB_EXACT_LONG.methodHandle();
            break;
        case "lmul":
            mh = JSType.MUL_EXACT_LONG.methodHandle();
            break;
        case "ldiv":
            mh = JSType.DIV_EXACT_LONG.methodHandle();
            break;
        case "lrem":
            mh = JSType.REM_EXACT_LONG.methodHandle();
            break;
        case "lneg":
            mh = JSType.NEGATE_EXACT_LONG.methodHandle();
            break;
        default:
            throw new AssertionError("unsupported math intrinsic");
        }
        return new ConstantCallSite(MH.insertArguments(mh, mh.type().parameterCount() - 1, programPoint));
    }

    /**
     * Returns a dynamic invoker for a specified dynamic operation using the public lookup. You can use this method to
     * create a method handle that when invoked acts completely as if it were a Nashorn-linked call site. An overview of
     * available dynamic operations can be found in the
     * <a href="https://github.com/szegedi/dynalink/wiki/User-Guide-0.6">Dynalink User Guide</a>, but we'll show few
     * examples here:
     * <ul>
     *   <li>Get a named property with fixed name:
     *     <pre>
     * MethodHandle getColor = Boostrap.createDynamicInvoker("dyn:getProp:color", Object.class, Object.class);
     * Object obj = ...; // somehow obtain the object
     * Object color = getColor.invokeExact(obj);
     *     </pre>
     *   </li>
     *   <li>Get a named property with variable name:
     *     <pre>
     * MethodHandle getProperty = Boostrap.createDynamicInvoker("dyn:getElem", Object.class, Object.class, String.class);
     * Object obj = ...; // somehow obtain the object
     * Object color = getProperty.invokeExact(obj, "color");
     * Object shape = getProperty.invokeExact(obj, "shape");
     * MethodHandle getNumProperty = Boostrap.createDynamicInvoker("dyn:getElem", Object.class, Object.class, int.class);
     * Object elem42 = getNumProperty.invokeExact(obj, 42);
     *     </pre>
     *   </li>
     *   <li>Set a named property with fixed name:
     *     <pre>
     * MethodHandle setColor = Boostrap.createDynamicInvoker("dyn:setProp:color", void.class, Object.class, Object.class);
     * Object obj = ...; // somehow obtain the object
     * setColor.invokeExact(obj, Color.BLUE);
     *     </pre>
     *   </li>
     *   <li>Set a property with variable name:
     *     <pre>
     * MethodHandle setProperty = Boostrap.createDynamicInvoker("dyn:setElem", void.class, Object.class, String.class, Object.class);
     * Object obj = ...; // somehow obtain the object
     * setProperty.invokeExact(obj, "color", Color.BLUE);
     * setProperty.invokeExact(obj, "shape", Shape.CIRCLE);
     *     </pre>
     *   </li>
     *   <li>Call a function on an object; two-step variant. This is the actual variant used by Nashorn-generated code:
     *     <pre>
     * MethodHandle findFooFunction = Boostrap.createDynamicInvoker("dyn:getMethod:foo", Object.class, Object.class);
     * Object obj = ...; // somehow obtain the object
     * Object foo_fn = findFooFunction.invokeExact(obj);
     * MethodHandle callFunctionWithTwoArgs = Boostrap.createDynamicInvoker("dyn:call", Object.class, Object.class, Object.class, Object.class, Object.class);
     * // Note: "call" operation takes a function, then a "this" value, then the arguments:
     * Object foo_retval = callFunctionWithTwoArgs.invokeExact(foo_fn, obj, arg1, arg2);
     *     </pre>
     *   </li>
     *   <li>Call a function on an object; single-step variant. Although Nashorn doesn't use this variant and never
     *   emits any INVOKEDYNAMIC instructions with {@code dyn:getMethod}, it still supports this standard Dynalink
     *   operation:
     *     <pre>
     * MethodHandle callFunctionFooWithTwoArgs = Boostrap.createDynamicInvoker("dyn:callMethod:foo", Object.class, Object.class, Object.class, Object.class);
     * Object obj = ...; // somehow obtain the object
     * Object foo_retval = callFunctionFooWithTwoArgs.invokeExact(obj, arg1, arg2);
     *     </pre>
     *   </li>
     * </ul>
     * Few additional remarks:
     * <ul>
     * <li>Just as Nashorn works with any Java object, the invokers returned from this method can also be applied to
     * arbitrary Java objects in addition to Nashorn JavaScript objects.</li>
     * <li>For invoking a named function on an object, you can also use the {@link InvokeByName} convenience class.</li>
     * <li>For Nashorn objects {@code getElem}, {@code getProp}, and {@code getMethod} are handled almost identically,
     * since JavaScript doesn't distinguish between different kinds of properties on an object. Either can be used with
     * fixed property name or a variable property name. The only significant difference is handling of missing
     * properties: {@code getMethod} for a missing member will link to a potential invocation of
     * {@code __noSuchMethod__} on the object, {@code getProp} for a missing member will link to a potential invocation
     * of {@code __noSuchProperty__}, while {@code getElem} for a missing member will link to an empty getter.</li>
     * <li>In similar vein, {@code setElem} and {@code setProp} are handled identically on Nashorn objects.</li>
     * <li>There's no rule that the variable property identifier has to be a {@code String} for {@code getProp/setProp}
     * and {@code int} for {@code getElem/setElem}. You can declare their type to be {@code int}, {@code double},
     * {@code Object}, and so on regardless of the kind of the operation.</li>
     * <li>You can be as specific in parameter types as you want. E.g. if you know that the receiver of the operation
     * will always be {@code ScriptObject}, you can pass {@code ScriptObject.class} as its parameter type. If you happen
     * to link to a method that expects different types, (you can use these invokers on POJOs too, after all, and end up
     * linking with their methods that have strongly-typed signatures), all necessary conversions allowed by either Java
     * or JavaScript will be applied: if invoked methods specify either primitive or wrapped Java numeric types, or
     * {@code String} or {@code boolean/Boolean}, then the parameters might be subjected to standard ECMAScript
     * {@code ToNumber}, {@code ToString}, and {@code ToBoolean} conversion, respectively. Less obviously, if the
     * expected parameter type is a SAM type, and you pass a JavaScript function, a proxy object implementing the SAM
     * type and delegating to the function will be passed. Linkage can often be optimized when linkers have more
     * specific type information than "everything can be an object".</li>
     * <li>You can also be as specific in return types as you want. For return types any necessary type conversion
     * available in either Java or JavaScript will be automatically applied, similar to the process described for
     * parameters, only in reverse direction:  if you specify any either primitive or wrapped Java numeric type, or
     * {@code String} or {@code boolean/Boolean}, then the return values will be subjected to standard ECMAScript
     * {@code ToNumber}, {@code ToString}, and {@code ToBoolean} conversion, respectively. Less obviously, if the return
     * type is a SAM type, and the return value is a JavaScript function, a proxy object implementing the SAM type and
     * delegating to the function will be returned.</li>
     * </ul>
     * @param opDesc Dynalink dynamic operation descriptor.
     * @param rtype the return type for the operation
     * @param ptypes the parameter types for the operation
     * @return MethodHandle for invoking the operation.
     */
    public static MethodHandle createDynamicInvoker(final String opDesc, final Class<?> rtype, final Class<?>... ptypes) {
        return createDynamicInvoker(opDesc, MethodType.methodType(rtype, ptypes));
    }

    /**
     * Returns a dynamic invoker for a specified dynamic operation using the public lookup. Similar to
     * {@link #createDynamicInvoker(String, Class, Class...)} but with an additional parameter to
     * set the call site flags of the dynamic invoker.
     * @param opDesc Dynalink dynamic operation descriptor.
     * @param flags the call site flags for the operation
     * @param rtype the return type for the operation
     * @param ptypes the parameter types for the operation
     * @return MethodHandle for invoking the operation.
     */
    public static MethodHandle createDynamicInvoker(final String opDesc, final int flags, final Class<?> rtype, final Class<?>... ptypes) {
        return bootstrap(MethodHandles.publicLookup(), opDesc, MethodType.methodType(rtype, ptypes), flags).dynamicInvoker();
    }

    /**
     * Returns a dynamic invoker for a specified dynamic operation using the public lookup. Similar to
     * {@link #createDynamicInvoker(String, Class, Class...)} but with return and parameter types composed into a
     * method type in the signature. See the discussion of that method for details.
     * @param opDesc Dynalink dynamic operation descriptor.
     * @param type the method type for the operation
     * @return MethodHandle for invoking the operation.
     */
    public static MethodHandle createDynamicInvoker(final String opDesc, final MethodType type) {
        return bootstrap(MethodHandles.publicLookup(), opDesc, type, 0).dynamicInvoker();
    }

    /**
     * Binds any object Nashorn can use as a [[Callable]] to a receiver and optionally arguments.
     * @param callable the callable to bind
     * @param boundThis the bound "this" value.
     * @param boundArgs the bound arguments. Can be either null or empty array to signify no arguments are bound.
     * @return a bound callable.
     * @throws ECMAException with {@code TypeError} if the object is not a callable.
     */
    public static Object bindCallable(final Object callable, final Object boundThis, final Object[] boundArgs) {
        if (callable instanceof ScriptFunctionImpl) {
            return ((ScriptFunctionImpl)callable).makeBoundFunction(boundThis, boundArgs);
        } else if (callable instanceof BoundCallable) {
            return ((BoundCallable)callable).bind(boundArgs);
        } else if (isCallable(callable)) {
            return new BoundCallable(callable, boundThis, boundArgs);
        }
        throw notFunction(callable);
    }

    /**
     * Creates a super-adapter for an adapter, that is, an adapter to the adapter that allows invocation of superclass
     * methods on it.
     * @param adapter the original adapter
     * @return a new adapter that can be used to invoke super methods on the original adapter.
     */
    public static Object createSuperAdapter(final Object adapter) {
        return new JavaSuperAdapter(adapter);
    }

    /**
     * If the given class is a reflection-specific class (anything in {@code java.lang.reflect} and
     * {@code java.lang.invoke} package, as well a {@link Class} and any subclass of {@link ClassLoader}) and there is
     * a security manager in the system, then it checks the {@code nashorn.JavaReflection} {@code RuntimePermission}.
     * @param clazz the class being tested
     * @param isStatic is access checked for static members (or instance members)
     */
    public static void checkReflectionAccess(final Class<?> clazz, final boolean isStatic) {
        ReflectionCheckLinker.checkReflectionAccess(clazz, isStatic);
    }

    /**
     * Returns the Nashorn's internally used dynamic linker's services object. Note that in code that is processing a
     * linking request, you will normally use the {@code LinkerServices} object passed by whatever top-level linker
     * invoked the linking (if the call site is in Nashorn-generated code, you'll get this object anyway). You should
     * only resort to retrieving a linker services object using this method when you need some linker services (e.g.
     * type converter method handles) outside of a code path that is linking a call site.
     * @return Nashorn's internal dynamic linker's services object.
     */
    public static LinkerServices getLinkerServices() {
        return dynamicLinker.getLinkerServices();
    }

    /**
     * Takes a guarded invocation, and ensures its method and guard conform to the type of the call descriptor, using
     * all type conversions allowed by the linker's services. This method is used by Nashorn's linkers as a last step
     * before returning guarded invocations. Most of the code used to produce the guarded invocations does not make an
     * effort to coordinate types of the methods, and so a final type adjustment before a guarded invocation is returned
     * to the aggregating linker is the responsibility of the linkers themselves.
     * @param inv the guarded invocation that needs to be type-converted. Can be null.
     * @param linkerServices the linker services object providing the type conversions.
     * @param desc the call site descriptor to whose method type the invocation needs to conform.
     * @return the type-converted guarded invocation. If input is null, null is returned. If the input invocation
     * already conforms to the requested type, it is returned unchanged.
     */
    static GuardedInvocation asTypeSafeReturn(final GuardedInvocation inv, final LinkerServices linkerServices, final CallSiteDescriptor desc) {
        return inv == null ? null : inv.asTypeSafeReturn(linkerServices, desc.getMethodType());
    }

    /**
     * Adapts the return type of the method handle with {@code explicitCastArguments} when it is an unboxing
     * conversion. This will ensure that nulls are unwrapped to false or 0.
     * @param target the target method handle
     * @param newType the desired new type. Note that this method does not adapt the method handle completely to the
     * new type, it only adapts the return type; this is allowed as per
     * {@link DynamicLinkerFactory#setAutoConversionStrategy(MethodTypeConversionStrategy)}, which is what this method
     * is used for.
     * @return the method handle with adapted return type, if it required an unboxing conversion.
     */
    private static MethodHandle unboxReturnType(final MethodHandle target, final MethodType newType) {
        final MethodType targetType = target.type();
        final Class<?> oldReturnType = targetType.returnType();
        final Class<?> newReturnType = newType.returnType();
        if (TypeUtilities.isWrapperType(oldReturnType)) {
            if (newReturnType.isPrimitive()) {
                // The contract of setAutoConversionStrategy is such that the difference between newType and targetType
                // can only be JLS method invocation conversions.
                assert TypeUtilities.isMethodInvocationConvertible(oldReturnType, newReturnType);
                return MethodHandles.explicitCastArguments(target, targetType.changeReturnType(newReturnType));
            }
        } else if (oldReturnType == void.class && newReturnType == Object.class) {
            return MethodHandles.filterReturnValue(target, VOID_TO_OBJECT);
        }
        return target;
    }
}
