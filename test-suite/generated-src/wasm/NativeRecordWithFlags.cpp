// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from enum_flags.djinni

#include "NativeRecordWithFlags.hpp"  // my header
#include "NativeAccessFlags.hpp"

namespace djinni_generated {

auto NativeRecordWithFlags::toCpp(const JsType& j) -> CppType {
    return {::djinni_generated::NativeAccessFlags::Boxed::toCpp(j["mAccess"])};
}
auto NativeRecordWithFlags::fromCpp(const CppType& c) -> JsType {
    em::val js = em::val::object();
    js.set("mAccess", ::djinni_generated::NativeAccessFlags::Boxed::fromCpp(c.access));
    return js;
}

}  // namespace djinni_generated
