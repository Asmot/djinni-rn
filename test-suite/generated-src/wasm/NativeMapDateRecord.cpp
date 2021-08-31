// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from date.djinni

#include "NativeMapDateRecord.hpp"  // my header
#include "djinni_wasm.hpp"

namespace djinni_generated {

auto NativeMapDateRecord::toCpp(const JsType& j) -> CppType {
    return {::djinni::Map<::djinni::String, ::djinni::Date>::Boxed::toCpp(j["mDatesById"])};
}
auto NativeMapDateRecord::fromCpp(const CppType& c) -> JsType {
    em::val js = em::val::object();
    js.set("mDatesById", ::djinni::Map<::djinni::String, ::djinni::Date>::Boxed::fromCpp(c.dates_by_id));
    return js;
}

}  // namespace djinni_generated
