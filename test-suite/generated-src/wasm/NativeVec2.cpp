// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from array.djinni

#include "NativeVec2.hpp"  // my header

namespace djinni_generated {

auto NativeVec2::toCpp(const JsType& j) -> CppType {
    return {::djinni::I32::Boxed::toCpp(j["mX"]),
            ::djinni::I32::Boxed::toCpp(j["mY"])};
}
auto NativeVec2::fromCpp(const CppType& c) -> JsType {
    em::val js = em::val::object();
    js.set("mX", ::djinni::I32::Boxed::fromCpp(c.x));
    js.set("mY", ::djinni::I32::Boxed::fromCpp(c.y));
    return js;
}

}  // namespace djinni_generated
