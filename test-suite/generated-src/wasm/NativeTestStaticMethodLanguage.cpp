// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from static_method_language.djinni

#include "NativeTestStaticMethodLanguage.hpp"  // my header

namespace djinni_generated {

em::val NativeTestStaticMethodLanguage::cppProxyMethods() {
    static const em::val methods = em::val::array(std::vector<std::string> {
    });
    return methods;
}


EMSCRIPTEN_BINDINGS(testsuite_test_static_method_language) {
    ::djinni::DjinniClass_<::testsuite::TestStaticMethodLanguage>("testsuite_TestStaticMethodLanguage", "testsuite.TestStaticMethodLanguage")
        .smart_ptr<std::shared_ptr<::testsuite::TestStaticMethodLanguage>>("testsuite_TestStaticMethodLanguage")
        .function("nativeDestroy", &NativeTestStaticMethodLanguage::nativeDestroy)
        ;
}

}  // namespace djinni_generated