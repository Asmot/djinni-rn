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


import scala.collection.mutable

import java.io.{File, FileNotFoundException, InputStreamReader, FileInputStream, Writer}
import java.io.StringWriter
/*
if is record, only generate toReadableMap and fromReadableMap

*/
class RNTsGenerator(spec: Spec) extends RNMUstacheGenerator(spec) {

  val templateDataMap = readTemplateFilesMap(spec.rn_tsTemplateFile.get) 

  override def getFileName(ident: Ident, typeParams: Seq[TypeParam], i: Interface) : String = {
    return marshal.typename(ident, i)
  }
  override def getTemplateData(annotation: Option[Annotation]) : String = {
    val key = annotation.get.value;
    return templateDataMap(key)
  }

  // no need to add null check
  override def getInterfaceRef(i: Interface) : JavaRefs = {
    val refs = new JavaRefs()
    i.methods.map(m => {
      m.annotation.getOrElse(None) match {
         case Annotation(ident, value) => {    
            m.params.map(p => {
            // if type is record add to  refs 
            // and have annotation
            p.ty.resolved.base match {
              case df: MDef => df.defType match {
                case DRecord => refs.java.add(s"${marshal.fieldType(p.ty)}");
                case DEnum => refs.java.add(s"${marshal.fieldType(p.ty)}");
                case _ => {}//throw new AssertionError("Unreachable")
              }
              
              case _ => {}//throw new AssertionError("Unreachable")
            }
          })
          // if return is record add to ref
          m.ret.getOrElse(None) match {
            case None => {}
            case _ => {
              m.ret.get.resolved.base match {
                case df: MDef => df.defType match {
                  case DRecord => refs.java.add(s"${marshal.fieldType(m.ret.get)}");
                  case DEnum => refs.java.add(s"${marshal.fieldType(m.ret.get)}");
                  case _ => {}//throw new AssertionError("Unreachable")
                }
                case _ => {}//throw new AssertionError("Unreachable")
              }
            }
          }
         }
         case None => {}
      }
    })
    return refs;
    
  }
  


  def writeFinalFile(ident: String, origin: String, refs: Iterable[String], f: IndentWriter => Unit) {
    createFile(spec.rn_tsOutFolder.get, idJava.ty(ident) + ".tsx", (w: IndentWriter) => {
      w.wl("// AUTOGENERATED FILE - DO NOT MODIFY!")
      w.wl("// This file was generated by Djinni from " + origin)
      w.wl
      if (refs.nonEmpty) {
        
        refs.foreach(s => {
          // hard code remove CheckForNull and Nonnull
          if (s"${s}" contains "javax.") {
          } else {
            w.wl(s"""import {${s}} from "./${s}";""")
          }
        })
        w.wl
      }
      f(w)
    })
  }

  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record) {   
  }
  override def generateRecord(origin: String, ident: Ident, doc: Doc, params: Seq[TypeParam], r: Record, annotation: Option[Annotation]) {
    val refs = new JavaRefs()
    refs.java.clear()

    // import all Record
    for (f <- r.fields) {
      f.ty.resolved.base match {
        case df: MDef => df.defType match {
          case DRecord => refs.java.add(s"${marshal.fieldType(f.ty)}");
          case DEnum => refs.java.add(s"${marshal.fieldType(f.ty)}");
          case _ => {}//throw new AssertionError("Unreachable")
        }
        
        case _ => {}//throw new AssertionError("Unreachable")
      }
      
    }

    r.fields.foreach(f => refs.find(f.ty))
    val className = if (r.ext.java) (ident.name + "_base") else (ident.name)
    
    writeFinalFile(className, origin, refs.java, w => {
      writeDoc(w, doc)
      javaAnnotationHeader.foreach(w.wl)
      val self = marshal.typename(className, r)

      w.w(s"export type ${className} =").braced {
        w.wl
        // Field definitions.
        for (f <- r.fields) {
          w.wl
          
          writeDoc(w, f.doc)
          // ${marshal.fieldType(f.ty)}
          w.w(s"${f.ident.name} ?: ")
          f.ty.resolved.base match {
            case MString | MDate => w.w(s"string")
            case t: MPrimitive => t.jName match {
                case "boolean" => w.w(s"boolean")
                case _ => w.w(s"number")
              }
            case df: MDef => df.defType match {
              case DRecord => w.w(s"${marshal.fieldType(f.ty)}")
              case DEnum => w.w(s"${marshal.fieldType(f.ty)}")
              case _ => {}//throw new AssertionError("Unreachable")
            }
           
            case _ => {}//throw new AssertionError("Unreachable")
          }
          w.wl(s";")
      
        }


      }
    })
  }


}
