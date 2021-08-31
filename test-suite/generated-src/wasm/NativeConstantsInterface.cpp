// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from constants.djinni

#include "NativeConstantsInterface.hpp"  // my header

namespace djinni_generated {

em::val NativeConstantsInterface::cppProxyMethods() {
    static const em::val methods = em::val::array(std::vector<std::string> {
        "dummy",
    });
    return methods;
}

void NativeConstantsInterface::dummy(const CppType& self) {
    return self->dummy();
}

void NativeConstantsInterface::JsProxy::dummy() {
    return _jsRef().call<void>("dummy");
}

EMSCRIPTEN_BINDINGS(constants_interface) {
    em::class_<::testsuite::ConstantsInterface>("ConstantsInterface")
        .smart_ptr<std::shared_ptr<::testsuite::ConstantsInterface>>("ConstantsInterface")
        .function("nativeDestroy", &NativeConstantsInterface::nativeDestroy)
        .function("dummy", NativeConstantsInterface::dummy)
        ;
}

}  // namespace djinni_generated
