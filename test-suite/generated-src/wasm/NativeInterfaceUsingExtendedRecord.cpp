// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from extended_record.djinni

#include "NativeInterfaceUsingExtendedRecord.hpp"  // my header
#include "NativeExtendedRecord.hpp"

namespace djinni_generated {

em::val NativeInterfaceUsingExtendedRecord::cppProxyMethods() {
    static const em::val methods = em::val::array(std::vector<std::string> {
        "meth",
    });
    return methods;
}

em::val NativeInterfaceUsingExtendedRecord::meth(const CppType& self, const em::val& w_er) {
    return ::djinni_generated::NativeExtendedRecord::fromCpp(self->meth(::djinni_generated::NativeExtendedRecord::toCpp(w_er)));
}

::testsuite::ExtendedRecord NativeInterfaceUsingExtendedRecord::JsProxy::meth(const ::testsuite::ExtendedRecord & er) {
    return ::djinni_generated::NativeExtendedRecord::toCpp(_jsRef().call<em::val>("meth", ::djinni_generated::NativeExtendedRecord::fromCpp(er)));
}

EMSCRIPTEN_BINDINGS(interface_using_extended_record) {
    em::class_<::testsuite::InterfaceUsingExtendedRecord>("InterfaceUsingExtendedRecord")
        .smart_ptr<std::shared_ptr<::testsuite::InterfaceUsingExtendedRecord>>("InterfaceUsingExtendedRecord")
        .function("nativeDestroy", &NativeInterfaceUsingExtendedRecord::nativeDestroy)
        .function("meth", NativeInterfaceUsingExtendedRecord::meth)
        ;
}

}  // namespace djinni_generated
