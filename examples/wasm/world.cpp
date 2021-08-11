#include <emscripten.h>
#include <emscripten/bind.h>

#include <iostream>
#include <map>

using namespace emscripten;

// library code
std::map<val, void*> jsProxyCache;
std::map<void*, val> cppProxyCache;

template<class I, class Self, class JsProxy>
struct JsInterface {
    static void nativeDestroy(const std::shared_ptr<I>& cpp) {
        std::cout << "delete entry from cppProxyCache" << std::endl;
        assert(cppProxyCache.find(cpp.get()) != cppProxyCache.end());
        cppProxyCache.erase(cpp.get());
    }
    static val _toJs(const std::shared_ptr<I>& c) {
        if (auto* p = dynamic_cast<JsProxy*>(c.get())) {
            // unwrap js object
            std::cout << "unwrap js object" << std::endl;
            return p->_jsRef();
        } else {
            auto i = cppProxyCache.find(c.get());
            if (i != cppProxyCache.end()) {
                // existing cpp proxy
                std::cout << "already has cpp proxy" << std::endl;
                return i->second.template call<val>("deref");
            } else {
                static val weakRefClass = val::global("WeakRef");
                val nativeRef(c);
                val cppProxy = Self::cppProxy().new_(nativeRef);
                val weakRef = weakRefClass.new_(cppProxy);
                cppProxyCache.emplace(c.get(), weakRef);
                static val finalizerRegistry = val::module_property("djinniFinalizerRegistry");
                finalizerRegistry.call<void>("register", cppProxy, nativeRef);
                return cppProxy;
            }
        }
    }
    static std::shared_ptr<I> _fromJs(const val& js) {
        static const val nativeRef("_nativeRef");
        if (nativeRef.in(js)) { // is cpp object
            std::cout << "getting cpp object" << std::endl;
            return js[nativeRef].as<std::shared_ptr<I>>();
        } else { // is jsproxy
            auto i = jsProxyCache.find(js);
            if (i != jsProxyCache.end()) {
                // existing js proxy
                std::cout << "existing js proxy" << std::endl;
                return reinterpret_cast<JsProxy*>(i->second)->shared_from_this();
            } else {
                return std::make_shared<JsProxy>(js);
            }
        }
    }
};

class JsProxyBase {
public:
    JsProxyBase(val v) : _js(std::move(v)) {
        std::cout << "+proxy" << std::endl;
        jsProxyCache[_js] = this;
    }

    virtual ~JsProxyBase() {
        std::cout << "~JsProxy" << std::endl;
        jsProxyCache.erase(_js);
    }

    const val& _jsRef() const {
        return _js;
    }
private:
    val _js;
};

// djinni generated interface
class MyInterface {
public:
    virtual ~MyInterface() = default;
    virtual void foo(int x) = 0;
    static std::shared_ptr<MyInterface> create();
    static std::shared_ptr<MyInterface> instance();
    static std::shared_ptr<MyInterface> pass(const std::shared_ptr<MyInterface>& i);
    static bool comp(const std::shared_ptr<MyInterface>& i, const std::shared_ptr<MyInterface>& j);
};

// djinni generated JS proxy
class MyInterface_JsProxy:public JsProxyBase,
                          public MyInterface,
                          public std::enable_shared_from_this<MyInterface_JsProxy> {
public:
    MyInterface_JsProxy(val v) : JsProxyBase(std::move(v)) {}
    
    void foo(int x) override {
        _jsRef().call<void>("foo", x);
    }
};

// djinni generated stubs
struct NativeMyInterface : JsInterface<MyInterface, NativeMyInterface, MyInterface_JsProxy> {
    static val cppProxy() {
        static val inst = val::module_property("MyInterface_CppProxy");
        return inst;
    }
    // ---------
    static void foo(const std::shared_ptr<MyInterface>& self, int x) {
        return self->foo(x);
    }
    static val create() {
        return _toJs(MyInterface::create());
    }
    static val instance() {
        return _toJs(MyInterface::instance());
    }
    static val pass(const val& i) {
        return _toJs(MyInterface::pass(_fromJs(i)));
    }
    static bool comp(const val& i, const val& j) {
        return MyInterface::comp(_fromJs(i), _fromJs(j));
    }
};

// djinni generated binding
EMSCRIPTEN_BINDINGS(MyInterface) {
    class_<MyInterface>("MyInterface")
        .smart_ptr<std::shared_ptr<MyInterface>>("MyInterface")
        .function("foo", &NativeMyInterface::foo)
        .class_function("create", &NativeMyInterface::create)
        .class_function("instance", &NativeMyInterface::instance)
        .class_function("pass", &NativeMyInterface::pass)
        .class_function("comp", &NativeMyInterface::comp)
        .function("nativeDestroy", &NativeMyInterface::nativeDestroy)
        ;
}

// user implementation
class MyInterfaceImpl : public MyInterface {
public:
    ~MyInterfaceImpl() override {
        std::cout << "~MyInterfaceImpl" << std::endl;
    }
    void foo(int x) override {
        std::cout << "MyInterfaceImpl::foo(" << x <<")" << std::endl;
    }
};

std::shared_ptr<MyInterface> MyInterface::create() {
    return std::make_shared<MyInterfaceImpl>();
}

std::shared_ptr<MyInterface> MyInterface::instance() {
    static auto singleton = std::make_shared<MyInterfaceImpl>();
    return singleton;
}

std::shared_ptr<MyInterface> MyInterface::pass(const std::shared_ptr<MyInterface>& i) {
    return i;
}

bool MyInterface::comp(const std::shared_ptr<MyInterface>& i, const std::shared_ptr<MyInterface>& j) {
    return i == j;
}
