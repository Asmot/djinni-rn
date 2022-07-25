/**
  * Copyright 2014 Dropbox, Inc.
  *
  * Licensed under the Apache License, Version 2.0 (the "License");
  * you may not use this file except in compliance with the License.
  * You may obtain a copy of the License at
  *
  *    http://www.apache.org/licenses/LICENSE-2.0
  *
  * Unless required by applicable law or agreed to in writing, software
  * distributed under the License is distributed on an "AS IS" BASIS,
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  * 
  * This file has been modified by Snap, Inc.
  */

package djinni

import djinni.ast.Record.DerivingType
import djinni.ast._
import djinni.generatorTools._
import djinni.meta._
import djinni.writer.IndentWriter

import scala.collection.mutable


/*
if is record, only generate toReadableMap and fromReadableMap

*/
class RNJavaGenerator(spec: Spec) extends Generator(spec) {

  val javaAnnotationHeader = spec.javaAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaNullableAnnotation = spec.javaNullableAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaNonnullAnnotation = spec.javaNonnullAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaClassAccessModifierString = JavaAccessModifier.getCodeGenerationString(spec.javaClassAccessModifier)
  val marshal = new JavaMarshal(spec)

  var PRE_STR = "SRN"

  class JavaRefs() {
    var java = mutable.TreeSet[String]()

    spec.javaAnnotation.foreach(pkg => java.add(pkg))
    spec.javaNullableAnnotation.foreach(pkg => java.add(pkg))
    spec.javaNonnullAnnotation.foreach(pkg => java.add(pkg))

    def find(ty: TypeRef) { find(ty.resolved) }
    def find(tm: MExpr) {
      tm.args.foreach(find)
      find(tm.base)
    }
    def find(m: Meta) = for(r <- marshal.references(m)) r match {
      case ImportRef(arg) => java.add(arg)
      case _ =>
    }
  }

  def writeJavaFile(ident: String, origin: String, refs: Iterable[String], f: IndentWriter => Unit) {
    createFile(spec.rn_javaOutFolder.get, idJava.ty(ident) + ".java", (w: IndentWriter) => {
      w.wl("// AUTOGENERATED FILE - DO NOT MODIFY!")
      w.wl("// This file was generated by Djinni from " + origin)
      w.wl
      spec.rn_javaPackage.foreach(s => w.wl(s"package $s;").wl)
      if (refs.nonEmpty) {
        refs.foreach(s => w.wl(s"import $s;"))
        w.wl
      }
      f(w)
    })
  }

  def generateJavaConstants(w: IndentWriter, consts: Seq[Const]) = {

    def writeJavaConst(w: IndentWriter, ty: TypeRef, v: Any): Unit = v match {
      case l: Long if marshal.fieldType(ty).equalsIgnoreCase("long") => w.w(l.toString + "l")
      case l: Long => w.w(l.toString)
      case d: Double if marshal.fieldType(ty).equalsIgnoreCase("float") => w.w(d.toString + "f")
      case d: Double => w.w(d.toString)
      case b: Boolean => w.w(if (b) "true" else "false")
      case s: String => w.w(s)
      case e: EnumValue =>  w.w(s"${marshal.typename(ty)}.${idJava.enum(e)}")
      case v: ConstRef => w.w(idJava.const(v))
      case z: Map[_, _] => { // Value is record
        val recordMdef = ty.resolved.base.asInstanceOf[MDef]
        val record = recordMdef.body.asInstanceOf[Record]
        val vMap = z.asInstanceOf[Map[String, Any]]
        w.wl(s"new ${marshal.typename(ty)}(")
        w.increase()
        // Use exact sequence
        val skipFirst = SkipFirst()
        for (f <- record.fields) {
          skipFirst {w.wl(",")}
          writeJavaConst(w, f.ty, vMap.apply(f.ident.name))
          w.w(" /* " + idJava.field(f.ident) + " */ ")
        }
        w.w(")")
        w.decrease()
      }
    }

    for (c <- consts) {
      writeDoc(w, c.doc)
      javaAnnotationHeader.foreach(w.wl)
      marshal.nullityAnnotation(c.ty).foreach(w.wl)
      w.w(s"public static final ${marshal.fieldType(c.ty)} ${idJava.const(c.ident)} = ")
      writeJavaConst(w, c.ty, c.value)
      w.wl(";")
      w.wl
    }
  }

  private val moduleClass: String = spec.javaIdentStyle.ty(spec.moduleName) + "Module"

  override def generateModule(decls: Seq[InternTypeDecl]) {
    if (spec.jniUseOnLoad) {
      writeJavaFile(moduleClass, s"${spec.moduleName} Module", List.empty, w => {
        w.wl(s"public final class $moduleClass").braced {
          w.wl("static").braced {
            w.wl("if (System.getProperty(\"java.vm.vendor\").equals(\"The Android Project\"))").braced {
              w.wl("Guard.initialize();")
            }
          }
          w.wl("private static final class Guard").braced {
            w.wl("private static native void initialize();")
          }
        }
      })
    }
  }

  override def generateEnum(origin: String, ident: Ident, doc: Doc, e: Enum) {
    val refs = new JavaRefs()

    writeJavaFile(ident, origin, refs.java, w => {
      writeDoc(w, doc)
      javaAnnotationHeader.foreach(w.wl)
      w.w(s"${javaClassAccessModifierString}enum ${marshal.typename(ident, e)}").braced {
        for (o <- normalEnumOptions(e)) {
          writeDoc(w, o.doc)
          w.wl(idJava.enum(o.ident) + ",")
        }
        w.wl(";")
      }
    })
  }

  override def generateInterface(origin: String, ident: Ident, doc: Doc, typeParams: Seq[TypeParam], i: Interface) {
    val refs = new JavaRefs()

    i.methods.map(m => {
      m.params.map(p => refs.find(p.ty))
      m.ret.foreach(refs.find)
    })
    i.consts.map(c => {
      refs.find(c.ty)
    })
    // if (i.ext.cpp) {
    //   refs.java.add("java.util.concurrent.atomic.AtomicBoolean")
    //   refs.java.add("com.snapchat.djinni.NativeObjectManager")
    // }

     // rn java
    refs.java.add("com.facebook.react.bridge.ReactApplicationContext");
    refs.java.add("com.facebook.react.bridge.ReadableMap");
    refs.java.add("com.facebook.react.uimanager.ViewGroupManager");
    refs.java.add("com.facebook.react.uimanager.annotations.ReactProp");
    refs.java.add("com.facebook.react.uimanager.ThemedReactContext");
    refs.java.add("android.content.Context");
    
    // for smap TODO add to spec
    refs.java.add("com.smap.maps.model.*");

    def writeModuleInitializer(w: IndentWriter) = {
      if (spec.jniUseOnLoad) {
        w.wl("static").braced {
          w.wl("try").braced {
            w.wl(s"Class.forName(${q(spec.javaPackage.getOrElse("") + "." + moduleClass)});")
          }
          w.wl("catch (ClassNotFoundException e)").braced {
            w.wl(s"throw new IllegalStateException(${q("Failed to initialize djinni module")}, e);")
          }
        }
      }
    }
    val javaClass = marshal.typename(ident, i)
    val typeParamList = javaTypeParams(typeParams)
    var javaName = s"${PRE_STR}$javaClass${typeParamList}Manager"
    var javaNameView = s"${PRE_STR}$javaClass"

    // inner View
    val viewName = javaClass
    val viewOptionsName = javaClass + "Options"
    val viewClassName = PRE_STR + javaClass
    

    writeJavaFile(javaName, origin, refs.java, w => {
      
      writeDoc(w, doc)

      javaAnnotationHeader.foreach(w.wl)
      w.w(s"${javaClassAccessModifierString} class ${javaName} extends ViewGroupManager<${javaName}.${javaNameView}>").braced {
        // pre text
        w.wl("ReactApplicationContext mCallerContext;")
        w.wl(s"""public static final String REACT_CLASS = "${viewClassName}Manager";""")
        w.wl("")
        w.wl(s"public ${viewClassName}Manager(ReactApplicationContext reactContext) {")
        w.wl("    this.mCallerContext = reactContext;")
        w.wl("}")
        w.wl("@Override")
        w.wl("public String getName() {")
        w.wl("    return REACT_CLASS;")
        w.wl("}")
        w.wl("@Override")
        w.wl(s"protected ${viewClassName} createViewInstance(ThemedReactContext reactContext) {")
        w.wl(s"  return new ${viewClassName}(reactContext, this);")
        w.wl("}") 

        val skipFirst = SkipFirst()
        generateJavaConstants(w, i.consts)

        val throwException = spec.javaCppException.fold("")(" throws " + _)

        // no return will set to prop
        for (m <- i.methods if !m.static) {
          // only generate with annotation
          // if have annotation generate a ReactProp name is the annotation value
          // and change the overlay value call the same function name
          m.annotation.getOrElse(None) match {
            case Annotation(ident, value) => {
              
              skipFirst { w.wl }
              writeMethodDoc(w, m, idJava.local)
              val ret = marshal.returnType(m.ret)
              val params = m.params.map(p => {
                val nullityAnnotation = marshal.nullityAnnotation(p.ty).map(_ + " ").getOrElse("")
                nullityAnnotation + marshal.paramType(p.ty) + " " + idJava.local(p.ident)
              })
              marshal.nullityAnnotation(m.ret).foreach(w.wl)

              if (m.params.length == 1) {
                val parm_field = m.params(0);

                w.wl(s"""@ReactProp(name = ${value})""")
                // react not support setPosition and setVisbile so use value to the function name
                val methodNameTemp = s"set_${value}"
                val methodName = methodNameTemp.replaceAll(""""""","")
                w.w(s"public void " + methodName + s"(${javaNameView} view, ReadableMap data)").braced {
                  // get value
                  parm_field.ty.resolved.base match {
                    case t: MPrimitive => t.jName match {
                      case "byte" | "short" | "int" | "float" | "double" | "long"   
                          => w.wl(s"""${t.jName} v = (${t.jName})data.getDouble("${parm_field.ident.name}");""")
                      case "boolean"
                          => w.wl(s"""${t.jName} v = data.getBoolean("${parm_field.ident.name}");""")
                    }
                    case df: MDef => df.defType match {
                      
                      case DRecord => w.wl(s"${marshal.paramType(parm_field.ty)} v = ${PRE_STR}${marshal.paramType(parm_field.ty)}.fromReadableMap(data);")
                    }
                    case _ => w.wl(s"// not support! ${parm_field.ident.name}")
                  }
                  // set value to native
                  w.wl("if (view.getMapOverlay() != null) {")
                  w.wl(s"    view.getMapOverlay().${m.ident.name}(v);")
                  w.wl("} else {")
                  w.wl(s"    view.getMapOverlayOptions().${parm_field.ident.name} = v;")
                  w.wl("}")
                }

              }
              
            }
            case None => {};
          }
          
        }

        // extends Map Feature
        // need add to Map, remove from and createView
        skipFirst { w.wl }
        w.w(s"public static class ${viewClassName} extends MapFeature<${viewName}, ${viewOptionsName}>").braced {
          w.wl(s"public ${viewClassName}(Context context, ${javaName} manager) {")
          w.wl("  super(context, manager);")
          w.wl("}")

          skipFirst { w.wl }
          w.wl(s"@Override")
          w.wl(s"public void addToMap(SMap map) {")
          w.wl(s"    overlay = map.add${viewName}(options);")
          w.wl(s"}")

          skipFirst { w.wl }
          w.wl(s"@Override")
          w.wl(s"public void removeFromMap(SMap map) {")
          w.wl(s"    // TODO: support remove")
          w.wl(s"}")

          skipFirst { w.wl }
          w.wl(s"@Override")
          w.wl(s"protected ${viewOptionsName} createView() {")
          w.wl(s"  return new ${viewOptionsName}();")
          w.wl(s"}")

        }

        // val statics = i.methods.filter(m => m.static && m.lang.java)

        // if (statics.nonEmpty) {
        //   writeModuleInitializer(w)
        // }
        // for (m <- statics) {
        //   skipFirst {
        //     w.wl
        //   }
        //   writeMethodDoc(w, m, idJava.local)
        //   val ret = marshal.returnType(m.ret)
        //   val params = m.params.map(p => {
        //     val nullityAnnotation = marshal.nullityAnnotation(p.ty).map(_ + " ").getOrElse("")
        //     nullityAnnotation + marshal.paramType(p.ty) + " " + idJava.local(p.ident)
        //   })
        //   marshal.nullityAnnotation(m.ret).foreach(w.wl)
        //   w.wl("public static native " + ret + " " + idJava.method(m.ident) + params.mkString("(", ", ", ")") + ";")
        // }

        // if (i.ext.cpp) {
        //   w.wl
        //   javaAnnotationHeader.foreach(w.wl)
        //   w.wl(s"public static final class CppProxy$typeParamList extends $javaClass$typeParamList").braced {
        //     writeModuleInitializer(w)
        //     w.wl("private final long nativeRef;")
        //     w.wl("private final AtomicBoolean destroyed = new AtomicBoolean(false);")
        //     w.wl
        //     w.wl(s"private CppProxy(long nativeRef)").braced {
        //       w.wl("if (nativeRef == 0) throw new RuntimeException(\"nativeRef is zero\");")
        //       w.wl("this.nativeRef = nativeRef;")
        //       w.wl("NativeObjectManager.register(this, nativeRef);")
        //     }
        //     w.wl("public static native void nativeDestroy(long nativeRef);")
        //     for (m <- i.methods if !m.static) { // Static methods not in CppProxy
        //       val ret = marshal.returnType(m.ret)
        //       val returnStmt = m.ret.fold("")(_ => "return ")
        //       val params = m.params.map(p => marshal.paramType(p.ty) + " " + idJava.local(p.ident)).mkString(", ")
        //       val args = m.params.map(p => idJava.local(p.ident)).mkString(", ")
        //       val meth = idJava.method(m.ident)
        //       w.wl
        //       w.wl(s"@Override")
        //       w.wl(s"public $ret $meth($params)$throwException").braced {
        //         w.wl("assert !this.destroyed.get() : \"trying to use a destroyed object\";")
        //         w.wl(s"${returnStmt}native_$meth(this.nativeRef${preComma(args)});")
        //       }
        //       w.wl(s"private native $ret native_$meth(long _nativeRef${preComma(params)});")
        //     }
        //   }
        // }
      }
    })
  }

  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record) {
    val refs = new JavaRefs()
    r.fields.foreach(f => refs.find(f.ty))

    // rn java
    refs.java.add("com.facebook.react.bridge.ReadableMap");
    refs.java.add("com.facebook.react.bridge.WritableMap");
    refs.java.add("com.facebook.react.bridge.WritableNativeMap");
    // for smap TODO add to spec
    refs.java.add("com.smap.maps.model.*");

    val javaName = if (r.ext.java) (ident.name + "_base") else (PRE_STR + ident.name)
    val javaFinal = if (!r.ext.java && spec.javaUseFinalForRecord) "public final " else ""

    writeJavaFile(javaName, origin, refs.java, w => {
      writeDoc(w, doc)
      javaAnnotationHeader.foreach(w.wl)
      val self = marshal.typename(javaName, r)

      w.w(s"${javaClassAccessModifierString}${javaFinal}class ${self + javaTypeParams(params)}").braced {
        w.wl
        generateJavaConstants(w, r.consts)
        // // Field definitions.
        // for (f <- r.fields) {
        //   w.wl
        //   w.wl(s"/*package*/ final ${marshal.fieldType(f.ty)} ${idJava.field(f.ident)};")
        // }

        // // Constructor.
        // w.wl
        // w.wl(s"public $self(").nestedN(2) {
        //   val skipFirst = SkipFirst()
        //   for (f <- r.fields) {
        //     skipFirst { w.wl(",") }
        //     marshal.nullityAnnotation(f.ty).map(annotation => w.w(annotation + " "))
        //     w.w(marshal.paramType(f.ty) + " " + idJava.local(f.ident))
        //   }
        //   w.wl(") {")
        // }
        // w.nested {
        //   for (f <- r.fields) {
        //     w.wl(s"this.${idJava.field(f.ident)} = ${idJava.local(f.ident)};")
        //   }
        // }
        // w.wl("}")

        // // Accessors
        // for (f <- r.fields) {
        //   w.wl
        //   writeDoc(w, f.doc)
        //   marshal.nullityAnnotation(f.ty).foreach(w.wl)
        //   w.w("public " + marshal.returnType(Some(f.ty)) + " " + idJava.method("get_" + f.ident.name) + "()").braced {
        //     w.wl("return " + idJava.field(f.ident) + ";")
        //   }
        // }

        // if (r.derivingTypes.contains(DerivingType.Eq)) {
        //   w.wl
        //   w.wl("@Override")
        //   val nullableAnnotation = javaNullableAnnotation.map(_ + " ").getOrElse("")
        //   w.w(s"public boolean equals(${nullableAnnotation}Object obj)").braced {
        //     w.w(s"if (!(obj instanceof $self))").braced {
        //       w.wl("return false;")
        //     }
        //     w.wl(s"$self other = ($self) obj;")
        //     w.w(s"return ").nestedN(2) {
        //       val skipFirst = SkipFirst()
        //       for (f <- r.fields) {
        //         skipFirst { w.wl(" &&") }
        //         f.ty.resolved.base match {
        //           case MBinary | MArray => w.w(s"java.util.Arrays.equals(${idJava.field(f.ident)}, other.${idJava.field(f.ident)})")
        //           case MList | MSet | MMap | MString | MDate => w.w(s"this.${idJava.field(f.ident)}.equals(other.${idJava.field(f.ident)})")
        //           case MOptional =>
        //             w.w(s"((this.${idJava.field(f.ident)} == null && other.${idJava.field(f.ident)} == null) || ")
        //             w.w(s"(this.${idJava.field(f.ident)} != null && this.${idJava.field(f.ident)}.equals(other.${idJava.field(f.ident)})))")
        //           case t: MPrimitive => w.w(s"this.${idJava.field(f.ident)} == other.${idJava.field(f.ident)}")
        //           case df: MDef => df.defType match {
        //             case DRecord => w.w(s"this.${idJava.field(f.ident)}.equals(other.${idJava.field(f.ident)})")
        //             case DEnum => w.w(s"this.${idJava.field(f.ident)} == other.${idJava.field(f.ident)}")
        //             case _ => throw new AssertionError("Unreachable")
        //           }
        //           case e: MExtern => e.defType match {
        //             case DRecord => if(e.java.reference) {
        //               w.w(s"this.${idJava.field(f.ident)}.equals(other.${idJava.field(f.ident)})")
        //             } else {
        //               w.w(s"this.${idJava.field(f.ident)} == other.${idJava.field(f.ident)}")
        //             }
        //             case DEnum => w.w(s"this.${idJava.field(f.ident)} == other.${idJava.field(f.ident)}")
        //             case _ => throw new AssertionError("Unreachable")
        //           }
        //           case _ => throw new AssertionError("Unreachable")
        //         }
        //       }
        //     }
        //     w.wl(";")
        //   }
        //   // Also generate a hashCode function, since you shouldn't override one without the other.
        //   // This hashcode implementation is based off of the apache commons-lang implementation of
        //   // HashCodeBuilder (excluding support for Java arrays) which is in turn based off of the
        //   // the recommendataions made in Effective Java.
        //   w.wl
        //   w.wl("@Override")
        //   w.w("public int hashCode()").braced {
        //     w.wl("// Pick an arbitrary non-zero starting value")
        //     w.wl("int hashCode = 17;")
        //     // Also pick an arbitrary prime to use as the multiplier.
        //     val multiplier = "31"
        //     for (f <- r.fields) {
        //       val fieldHashCode = f.ty.resolved.base match {
        //         case MBinary | MArray => s"java.util.Arrays.hashCode(${idJava.field(f.ident)})"
        //         case MList | MSet | MMap | MString | MDate => s"${idJava.field(f.ident)}.hashCode()"
        //         // Need to repeat this case for MDef
        //         case df: MDef => s"${idJava.field(f.ident)}.hashCode()"
        //         case MOptional => s"(${idJava.field(f.ident)} == null ? 0 : ${idJava.field(f.ident)}.hashCode())"
        //         case t: MPrimitive => t.jName match {
        //           case "byte" | "short" | "int" => idJava.field(f.ident)
        //           case "long" => s"((int) (${idJava.field(f.ident)} ^ (${idJava.field(f.ident)} >>> 32)))"
        //           case "float" => s"Float.floatToIntBits(${idJava.field(f.ident)})"
        //           case "double" => s"((int) (Double.doubleToLongBits(${idJava.field(f.ident)}) ^ (Double.doubleToLongBits(${idJava.field(f.ident)}) >>> 32)))"
        //           case "boolean" => s"(${idJava.field(f.ident)} ? 1 : 0)"
        //           case _ => throw new AssertionError("Unreachable")
        //         }
        //         case e: MExtern => e.defType match {
        //           case DRecord => "(" + e.java.hash.format(idJava.field(f.ident)) + ")"
        //           case DEnum => s"${idJava.field(f.ident)}.hashCode()"
        //           case _ => throw new AssertionError("Unreachable")
        //         }
        //         case _ => throw new AssertionError("Unreachable")
        //       }
        //       w.wl(s"hashCode = hashCode * $multiplier + $fieldHashCode;")
        //     }
        //     w.wl(s"return hashCode;")
        //   }
        // }

        // w.wl
        // w.wl("@Override")
        // w.w("public String toString()").braced {
        //   w.w(s"return ").nestedN(2) {
        //     w.wl(s""""${self}{" +""")
        //     for (i <- 0 to r.fields.length-1) {
        //       val name = idJava.field(r.fields(i).ident)
        //       val comma = if (i > 0) """"," + """ else ""
        //       w.wl(s"""${comma}"${name}=" + ${name} +""")
        //     }
        //   }
        //   w.wl(s""""}";""")
        // }
        // w.wl

        // toWritableMap
        w.wl
        w.w(s"public static WritableMap toWritableMap(${ident.name} item)" ).braced {
          w.wl("if (item == null) {return null;}")
          w.wl("WritableMap result = new WritableNativeMap();")
          for (f <- r.fields) {
            f.ty.resolved.base match {
              case t: MPrimitive => t.jName match {
                case "byte" | "short" | "int" | "float" | "double" | "long"   
                    => w.wl(s"""result.putDouble("${f.ident.name}", item.${f.ident.name});""")
                case "boolean"
                    => w.wl(s"""result.putBoolean("${f.ident.name}", item.${f.ident.name});""")
                    
              }
              case df: MDef => df.defType match {
                case DRecord => w.wl(s"""result.putMap("${f.ident.name}", ${PRE_STR}${marshal.typename(f.ty)}.toWritableMap(item.${f.ident.name}));""")
                case _ => w.wl(s"// not support! ${f.ident.name}")//throw new AssertionError("Unreachable")
              }
              case _ => w.wl(s"// not support! ${f.ident.name}")
            }
          }
          w.wl("return result;")
        }
        
        // fromReadableMap

        // convert readableMap to java object ,with hasKey check
        // eg result.tilt = (float)data.getDouble("tilt");  
        def fromReadableMapHasKeyCheck = (fieldName:String, castFieldType : String, isBool: Boolean) => {
          if (isBool) {
            w.wl(s"""if (data.hasKey("${fieldName}")) {""")
            w.wl(s"""   result.${fieldName} = data.getBoolean("${fieldName}");""")
            w.wl("}")
          } else {
            w.wl(s"""if (data.hasKey("${fieldName}")) {""")
            w.wl(s"""   result.${fieldName} = (${castFieldType})data.getDouble("${fieldName}");""")
            w.wl("}")
          }  
        }

        w.wl
        w.w(s"public static ${ident.name} fromReadableMap(ReadableMap data)" ).braced {
          w.wl("if (data == null) {return null;}")
          w.wl(s"${ident.name} result = new ${ident.name}();")
          for (f <- r.fields) {
            f.ty.resolved.base match {
              case t: MPrimitive => t.jName match {
                case "byte" | "short" | "double" | "long"   
                    => fromReadableMapHasKeyCheck(s"${f.ident.name}", "double", false)
                case "float" => fromReadableMapHasKeyCheck(s"${f.ident.name}", "float", false)
                case "int" => fromReadableMapHasKeyCheck(s"${f.ident.name}", "int", false)
                case "boolean" => fromReadableMapHasKeyCheck(s"${f.ident.name}", "boolean", true)
              }
              case df: MDef => df.defType match {
                case DRecord => 
                    w.wl(s"""if (data.hasKey("${f.ident.name}")) {""")
                    w.wl(s"""   result.${f.ident.name} = ${PRE_STR}${marshal.typename(f.ty)}.fromReadableMap(data.getMap("${f.ident.name}"));""")
                    w.wl(s"}")
                case _ => w.wl(s"// not support! ${f.ident.name}")
              }
              case _ => w.wl(s"// not support! ${f.ident.name}")
            }
          }
          w.wl("return result;")
        }

        if (spec.javaImplementAndroidOsParcelable && r.derivingTypes.contains(DerivingType.AndroidParcelable))
          writeParcelable(w, self, r);

        if (r.derivingTypes.contains(DerivingType.Ord)) {
          def primitiveCompare(ident: Ident) {
            w.wl(s"if (this.${idJava.field(ident)} < other.${idJava.field(ident)}) {").nested {
              w.wl(s"tempResult = -1;")
            }
            w.wl(s"} else if (this.${idJava.field(ident)} > other.${idJava.field(ident)}) {").nested {
              w.wl(s"tempResult = 1;")
            }
            w.wl(s"} else {").nested {
              w.wl(s"tempResult = 0;")
            }
            w.wl("}")
          }
          w.wl
          w.wl("@Override")
          val nonnullAnnotation = javaNonnullAnnotation.map(_ + " ").getOrElse("")
          w.w(s"public int compareTo($nonnullAnnotation$self other) ").braced {
            w.wl("int tempResult;")
            for (f <- r.fields) {
              f.ty.resolved.base match {
                case MString | MDate => w.wl(s"tempResult = this.${idJava.field(f.ident)}.compareTo(other.${idJava.field(f.ident)});")
                case t: MPrimitive => primitiveCompare(f.ident)
                case df: MDef => df.defType match {
                  case DRecord => w.wl(s"tempResult = this.${idJava.field(f.ident)}.compareTo(other.${idJava.field(f.ident)});")
                  case DEnum => w.w(s"tempResult = this.${idJava.field(f.ident)}.compareTo(other.${idJava.field(f.ident)});")
                  case _ => throw new AssertionError("Unreachable")
                }
                case e: MExtern => e.defType match {
                  case DRecord => if(e.java.reference) w.wl(s"tempResult = this.${idJava.field(f.ident)}.compareTo(other.${idJava.field(f.ident)});") else primitiveCompare(f.ident)
                  case DEnum => w.w(s"tempResult = this.${idJava.field(f.ident)}.compareTo(other.${idJava.field(f.ident)});")
                  case _ => throw new AssertionError("Unreachable")
                }
                case _ => throw new AssertionError("Unreachable")
              }
              w.w("if (tempResult != 0)").braced {
                w.wl("return tempResult;")
              }
            }
            w.wl("return 0;")
          }
        }

      }
    })
  }

  def javaTypeParams(params: Seq[TypeParam]): String =
    if (params.isEmpty) "" else params.map(p => idJava.typeParam(p.ident)).mkString("<", ", ", ">")

  def writeParcelable(w: IndentWriter, self: String, r: Record) = {
    // Generates the methods and the constructor to implement the interface android.os.Parcelable

    // CREATOR
    w.wl
    w.wl(s"public static final android.os.Parcelable.Creator<$self> CREATOR")
    w.w(s"    = new android.os.Parcelable.Creator<$self>()").bracedSemi {
      w.wl("@Override")
      w.w(s"public $self createFromParcel(android.os.Parcel in)").braced {
        w.wl(s"return new $self(in);")
      }
      w.wl
      w.wl("@Override")
      w.w(s"public $self[] newArray(int size)").braced {
        w.wl(s"return new $self[size];")
      }
    }

    // constructor (Parcel)
    def deserializeField(f: Field, m: Meta, inOptional: Boolean) {
      m match {
        case MString => w.wl(s"this.${idJava.field(f.ident)} = in.readString();")
        case MBinary => {
          w.wl(s"this.${idJava.field(f.ident)} = in.createByteArray();")
        }
        case MDate => w.wl(s"this.${idJava.field(f.ident)} = new ${marshal.typename(f.ty)}(in.readLong());")
        case t: MPrimitive => t.jName match {
          case "short" => w.wl(s"this.${idJava.field(f.ident)} = (short)in.readInt();")
          case "int" => w.wl(s"this.${idJava.field(f.ident)} = in.readInt();")
          case "long" => w.wl(s"this.${idJava.field(f.ident)} = in.readLong();")
          case "byte" => w.wl(s"this.${idJava.field(f.ident)} = in.readByte();")
          case "boolean" => w.wl(s"this.${idJava.field(f.ident)} = in.readByte() != 0;")
          case "float" => w.wl(s"this.${idJava.field(f.ident)} = in.readFloat();")
          case "double" => w.wl(s"this.${idJava.field(f.ident)} = in.readDouble();")
          case _ => throw new AssertionError("Unreachable")
        }
        case df: MDef => df.defType match {
          case DRecord => w.wl(s"this.${idJava.field(f.ident)} = new ${marshal.typename(f.ty)}(in);")
          case DEnum => w.wl(s"this.${idJava.field(f.ident)} = ${marshal.typename(f.ty)}.values()[in.readInt()];")
          case _ => throw new AssertionError("Unreachable")
        }
        case e: MExtern => e.defType match {
          case DRecord => w.wl(s"this.${idJava.field(f.ident)} = ${e.java.readFromParcel.format(marshal.typename(f.ty))};")
          case DEnum => w.wl(s"this.${idJava.field(f.ident)} = ${marshal.typename(f.ty)}.values()[in.readInt()];")
          case _ => throw new AssertionError("Unreachable")
        }
        case MList => {
          w.wl(s"this.${idJava.field(f.ident)} = new ${marshal.typename(f.ty)}();")
          w.wl(s"in.readList(this.${idJava.field(f.ident)}, getClass().getClassLoader());")
        }
        case MSet =>  {
          val collectionTypeName = marshal.typename(f.ty).replaceFirst("HashSet<(.*)>", "$1")
          w.wl(s"ArrayList<${collectionTypeName}> ${idJava.field(f.ident)}Temp = new ArrayList<${collectionTypeName}>();")
          w.wl(s"in.readList(${idJava.field(f.ident)}Temp, getClass().getClassLoader());")
          w.wl(s"this.${idJava.field(f.ident)} = new ${marshal.typename(f.ty)}(${idJava.field(f.ident)}Temp);")
        }
        case MMap => {
          w.wl(s"this.${idJava.field(f.ident)} = new ${marshal.typename(f.ty)}();")
          w.wl(s"in.readMap(this.${idJava.field(f.ident)}, getClass().getClassLoader());")
        }
        case MOptional => {
          if (inOptional)
          	throw new AssertionError("nested optional?")
          w.wl("if (in.readByte() == 0) {").nested {
            w.wl(s"this.${idJava.field(f.ident)} = null;")
          }
          w.wl("} else {").nested {
            deserializeField(f, f.ty.resolved.args.head.base, true)
          }
          w.wl("}")
        }
        case _ => throw new AssertionError("Unreachable")
      }
    }
    w.wl
    w.w(s"public $self(android.os.Parcel in)").braced {
      for (f <- r.fields)
        deserializeField(f, f.ty.resolved.base, false)
    }

    // describeContents
    w.wl
    w.wl("@Override")
    w.w("public int describeContents()").braced {
      w.wl("return 0;")
    }

    // writeToParcel
    def serializeField(f: Field, m: Meta, inOptional: Boolean) {
      m match {
        case MString => w.wl(s"out.writeString(this.${idJava.field(f.ident)});")
        case MBinary => {
          w.wl(s"out.writeByteArray(this.${idJava.field(f.ident)});")
        }
        case MDate => w.wl(s"out.writeLong(this.${idJava.field(f.ident)}.getTime());")
        case t: MPrimitive => t.jName match {
          case "short" | "int" => w.wl(s"out.writeInt(this.${idJava.field(f.ident)});")
          case "long" => w.wl(s"out.writeLong(this.${idJava.field(f.ident)});")
          case "byte" => w.wl(s"out.writeByte(this.${idJava.field(f.ident)});")
          case "boolean" => w.wl(s"out.writeByte(this.${idJava.field(f.ident)} ? (byte)1 : 0);")
          case "float" => w.wl(s"out.writeFloat(this.${idJava.field(f.ident)});")
          case "double" => w.wl(s"out.writeDouble(this.${idJava.field(f.ident)});")
          case _ => throw new AssertionError("Unreachable")
        }
        case df: MDef => df.defType match {
          case DRecord => w.wl(s"this.${idJava.field(f.ident)}.writeToParcel(out, flags);")
          case DEnum => w.wl(s"out.writeInt(this.${idJava.field(f.ident)}.ordinal());")
          case _ => throw new AssertionError("Unreachable")
        }
        case e: MExtern => e.defType match {
          case DRecord => w.wl(e.java.writeToParcel.format(idJava.field(f.ident)) + ";")
          case DEnum => w.wl(s"out.writeInt(this.${idJava.field(f.ident)}.ordinal());")
          case _ => throw new AssertionError("Unreachable")
        }
        case MList => {
          w.wl(s"out.writeList(this.${idJava.field(f.ident)});")
        }
        case MSet => {
          val collectionTypeName = marshal.typename(f.ty).replaceFirst("HashSet<(.*)>", "$1")
          w.wl(s"out.writeList(new ArrayList<${collectionTypeName}>(this.${idJava.field(f.ident)}));")
        }
        case MMap => w.wl(s"out.writeMap(this.${idJava.field(f.ident)});")
        case MOptional => {
          if (inOptional)
          	throw new AssertionError("nested optional?")
          w.wl(s"if (this.${idJava.field(f.ident)} != null) {").nested {
            w.wl("out.writeByte((byte)1);")
            serializeField(f, f.ty.resolved.args.head.base, true)
          }
          w.wl("} else {").nested {
            w.wl("out.writeByte((byte)0);")
          }
          w.wl("}")
        }
        case _ => throw new AssertionError("Unreachable")
      }
    }

    w.wl
    w.wl("@Override")
    w.w("public void writeToParcel(android.os.Parcel out, int flags)").braced {
      for (f <- r.fields)
        serializeField(f, f.ty.resolved.base, false)
    }
    w.wl
  }

}
