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
import djinni.utils._
import mustache._
import scala.util.parsing.json._

import scala.collection.mutable

import java.io.{File, FileNotFoundException, InputStreamReader, FileInputStream, Writer}
import java.io.StringWriter
/*
  generate all functions to a json data
*/
abstract class RNMUstacheGenerator(spec: Spec) extends Generator(spec) {

  val javaAnnotationHeader = spec.javaAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaNullableAnnotation = spec.javaNullableAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaNonnullAnnotation = spec.javaNonnullAnnotation.map(pkg => '@' + pkg.split("\\.").last)
  val javaClassAccessModifierString = JavaAccessModifier.getCodeGenerationString(spec.javaClassAccessModifier)
  val marshal = new JavaMarshal(spec)

  // TemplateFile is a json, read the all data to a map

  def readTemplateFilesMap(configFile : File): scala.collection.mutable.Map[String, String] = {
    val fileDir = configFile.getParent();
    val configJson = utils.readFileCon(configFile);

    val result = JSON.parseFull(configJson)
    var resultMap = scala.collection.mutable.Map[String, String]();
    result match {
      case Some(map: Map[Any, Any]) => {
        for (key <- map.keys) {
          val realPath = fileDir + "/" + map(key);
          val con = utils.readFileCon(realPath);
          resultMap.put(s""""${key}"""", con)
        }
      }
      case _ => System.out.println("invalid config")
    }

    
    return resultMap;
  }

  // child clsss support the template
  var rnJavaTemplate = "";

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

  def writeFinalFile(ident: String, origin: String, refs: Iterable[String], f: IndentWriter => Unit);

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
      writeFinalFile(moduleClass, s"${spec.moduleName} Module", List.empty, w => {
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
    // enum no need to generate again can use the java directily
  }

  // for interface
  def getFileName(ident: Ident, typeParams: Seq[TypeParam], i: Interface) : String;

  // for record
  def getFileName(ident: Ident, r: Record) : String;

  // for recrod
  def getRecordRefs(r : Record) : JavaRefs = {
    val refs = new JavaRefs()
    r.fields.foreach(f => refs.find(f.ty));
    return refs;
  }

  // different annotation will use different template data
  def getTemplateData(annotation: Option[Annotation]) : String;

  def getInterfaceRef(i: Interface) : JavaRefs = {
     val refs = new JavaRefs()
      i.methods.map(m => {
        m.params.map(p => refs.find(p.ty))
        m.ret.foreach(refs.find)
      })
      i.consts.map(c => {
        refs.find(c.ty)
      })
      return refs;
  }
  
  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record) {}
  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record, annotation: Option[Annotation]) {
    val refs = getRecordRefs(r);
    val templateData = getTemplateData(annotation);
    val template = new Mustache(templateData)
    var jsonDataMap = scala.collection.mutable.Map(
      "className" -> ident.name,
      "fields" -> List[scala.collection.mutable.Map[String, Any]]()
    )
    // class annotation
    jsonDataMap(s"${annotation.get.name.name}Annotation") = true;
    // remmove ""
    jsonDataMap("classAnnotaionValue") = annotation.get.value.replaceAll(""""""","")

    var jsonDataFields = List[scala.collection.mutable.Map[String, Any]]()

    val javaName = getFileName(ident, r)
    
    writeFinalFile(javaName, origin, refs.java, w => {
      writeDoc(w, doc)
      javaAnnotationHeader.foreach(w.wl)
      val self = marshal.typename(javaName, r)
      
      for (f <- r.fields) {

        val jsonDataProp = scala.collection.mutable.Map[String, Any]();

        val docWriter = new StringWriter();
        val innerW = new IndentWriter(docWriter);
        writeDoc(innerW, f.doc)
        // doce
        jsonDataProp.put("fieldDoc" , docWriter.toString());

        // field name 
        jsonDataProp("fieldName") = f.ident.name;
        jsonDataProp("fieldType") = marshal.typename(f.ty);
        
        f.ty.resolved.base match {
          case t: MPrimitive => t.jName match {
            case "byte" | "short" | "int" | "float" | "double" | "long"   
                => jsonDataProp("fieldIsNumber") = true;
            case "boolean"
                => jsonDataProp("fieldIsBool") = true;
                
          }
          case df: MDef => df.defType match {
            case DRecord => jsonDataProp("fieldIsObject") = true;
            case _ => {}//w.wl(s"// not support! ${f.ident.name}")//throw new AssertionError("Unreachable")
          }
          case _ => {}//w.wl(s"// not support! ${f.ident.name}")
        }
        jsonDataFields = jsonDataFields :+ jsonDataProp;
      }
      jsonDataMap("fields") = jsonDataFields;


      val formatedOutput = template.render(jsonDataMap)
      // System.out.println(jsonDataMap)
      w.wl(formatedOutput)
    })
  }

  override def generateInterface(origin: String, ident: Ident, doc: Doc, typeParams: Seq[TypeParam], i: Interface) {
    // only deal the interface which have annotation
  }
  override def generateInterface(origin: String, ident: Ident, doc: Doc, typeParams: Seq[TypeParam], i: Interface, annotation: Option[Annotation]) {
    val refs = getInterfaceRef(i);

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
    var javaFileName = getFileName(ident, typeParams, i); 
    
    val templateData = getTemplateData(annotation);
    val template = new Mustache(templateData)
    var jsonDataMap = scala.collection.mutable.Map(
      "className" -> javaClass,
      "functions" -> List[scala.collection.mutable.Map[String, Any]]()
    )
    // class annotation
    jsonDataMap(s"${annotation.get.name.name}Annotation") = true;
    // remmove ""
    jsonDataMap("classAnnotaionValue") = annotation.get.value.replaceAll(""""""","")

    var jsonDataFunctions = List[scala.collection.mutable.Map[String, Any]]()
    writeFinalFile(javaFileName, origin, refs.java, w => {        
      
      var counter = 1;
      val throwException = spec.javaCppException.fold("")(" throws " + _)
      // no return will set to prop
      for (m <- i.methods if !m.static) {
        // only generate with annotation
        // if have annotation generate a ReactProp name is the annotation value
        // and change the overlay value call the same function name
        m.annotation.getOrElse(None) match {
          case Annotation(ident, value) => {    

            val jsonDataProp = scala.collection.mutable.Map[String, Any]();

            val docWriter = new StringWriter();
            val innerW = new IndentWriter(docWriter);
            writeMethodDoc(innerW, m, idJava.local)
            // doce
            jsonDataProp.put("functionDoc" , docWriter.toString());
            // annotation
            jsonDataProp(s"${ident.name}Annotation") = true;
             // remmove ""
            jsonDataProp("annotaionValue") = value.replaceAll(""""""","")

            // function name and index (id)
            jsonDataProp("functionName") = m.ident.name;
            jsonDataProp("functionNameId") = counter;
            counter = counter + 1;

            // return
            val ret = marshal.returnType(m.ret)

            m.ret.getOrElse(None) match {
              case TypeRef(resolved) => {
                  jsonDataProp("haveReturn") = true;
                  jsonDataProp("returnType") = ret;
                  m.ret.get.resolved.base match {
                    case t: MPrimitive => t.jName match {
                      case "byte" | "short" | "int" | "float" | "double" | "long" => {
                        jsonDataProp("returnIsNumber") = true
                      }
                      case "boolean" => jsonDataProp("returnIsBool") = true
                    }
                    case df: MDef => df.defType match {
                      case DRecord => jsonDataProp("returnIsObject") = true
                    }
                  }
                }
              case None => jsonDataProp("haveReturn") = false;
            }
            
            val params = m.params.map(p => {
              val nullityAnnotation = marshal.nullityAnnotation(p.ty).map(_ + " ").getOrElse("")
              nullityAnnotation + marshal.paramType(p.ty) + " " + idJava.local(p.ident)
            })
            marshal.nullityAnnotation(m.ret).foreach(w.wl)

            // params
            jsonDataProp("haveParams") = (m.params.length > 0);
            jsonDataProp("oneParam") = (m.params.length == 1);
            jsonDataProp("params") = List[scala.collection.mutable.Map[String, Any]]();            

            var jsonDataParams = List[scala.collection.mutable.Map[String, Any]]();            
            var parmCounter = 0;
            var parmSize = m.params.length
            for (parm <- m.params) {
              val parm_field = parm;

              var jsonDataParm = scala.collection.mutable.Map[String, Any]();
              jsonDataParm("paramName") = parm_field.ident.name
              jsonDataParm("paramType") = marshal.paramType(parm_field.ty)
              
              parm_field.ty.resolved.base match {
                case t: MPrimitive => t.jName match {
                  case "byte" | "short" | "int" | "float" | "double" | "long" => {
                    jsonDataParm("paramIsNumber") = true
                  }
                  case "boolean" => jsonDataParm("paramIsBool") = true
                }
                case df: MDef => df.defType match {
                  case DRecord => jsonDataParm("paramIsObject") = true
                } 
                case MList => {
                  jsonDataParm("paramIsObject") = true
                  System.out.println(jsonDataParm)
                }
              }
              // record the param is first or last
              if (parmCounter == 0) {
                jsonDataParm("firstParam") = true;
              }
              if (parmCounter == parmSize - 1) {
                jsonDataParm("lastParam") = true;
              }
              jsonDataParm("paramIndex") = parmCounter;
              parmCounter = parmCounter + 1;
              jsonDataParams = jsonDataParams :+ jsonDataParm;
            }
            jsonDataProp("params") = jsonDataParams;
            jsonDataFunctions = jsonDataFunctions :+ jsonDataProp;
            
            
          }
          case None => {};
        }
        
      }
      jsonDataMap("functions") = jsonDataFunctions;
      val formatedOutput = template.render(jsonDataMap)
      // System.out.println(jsonDataMap)
      w.wl(formatedOutput)
      
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
