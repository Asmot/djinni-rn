// AUTOGENERATED FILE - DO NOT MODIFY!
// This file generated by Djinni from example.djinni

#include "NativeConversation.hpp"  // my header
#include "Marshal.hpp"

namespace djinni_generated {

NativeConversation::NativeConversation() = default;

NativeConversation::~NativeConversation() = default;

auto NativeConversation::fromCpp(JNIEnv* jniEnv, const CppType& c) -> ::djinni::LocalRef<JniType> {
    const auto& data = ::djinni::JniClass<NativeConversation>::get();
    auto r = ::djinni::LocalRef<JniType>{jniEnv->NewObject(data.clazz.get(), data.jconstructor,
                                                           ::djinni::get(::djinni::Binary::fromCpp(jniEnv, c.id)))};
    ::djinni::jniExceptionCheck(jniEnv);
    return r;
}

auto NativeConversation::toCpp(JNIEnv* jniEnv, JniType j) -> CppType {
    ::djinni::JniLocalScope jscope(jniEnv, 2);
    assert(j != nullptr);
    const auto& data = ::djinni::JniClass<NativeConversation>::get();
    return {::djinni::Binary::toCpp(jniEnv, (jbyteArray)jniEnv->GetObjectField(j, data.field_mId))};
}

}  // namespace djinni_generated