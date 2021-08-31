// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from derivings.djinni

#include "NativeRecordWithNestedDerivings.hpp"  // my header
#include "NativeRecordWithDerivings.hpp"

namespace djinni_generated {

auto NativeRecordWithNestedDerivings::toCpp(const JsType& j) -> CppType {
    return {::djinni::I32::Boxed::toCpp(j["mKey"]),
            ::djinni_generated::NativeRecordWithDerivings::Boxed::toCpp(j["mRec"])};
}
auto NativeRecordWithNestedDerivings::fromCpp(const CppType& c) -> JsType {
    em::val js = em::val::object();
    js.set("mKey", ::djinni::I32::Boxed::fromCpp(c.key));
    js.set("mRec", ::djinni_generated::NativeRecordWithDerivings::Boxed::fromCpp(c.rec));
    return js;
}

}  // namespace djinni_generated
