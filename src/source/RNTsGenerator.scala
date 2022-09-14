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
  
  override def getFileName(ident: Ident, r: Record) : String = {
    return s"${ident.name}"
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
              case MList => {
                // if is list paramType will be the type in <T>
                refs.java.add(s"${marshal.paramType(p.ty.resolved.args.head)}");
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

  // import all Record
  override def getRecordRefs(r : Record) : JavaRefs = {
    val refs = super.getRecordRefs(r);
    refs.java.clear()
    // import all Record
    for (f <- r.fields) {
      f.ty.resolved.base match {
        case df: MDef => df.defType match {
          case DRecord => refs.java.add(s"${marshal.fieldType(f.ty)}");
          case DEnum => refs.java.add(s"${marshal.fieldType(f.ty)}");
          case _ => {}//throw new AssertionError("Unreachable")
        }
        case MList => {
          // if is list paramType will be the type in <T>
          refs.java.add(s"${marshal.fieldType(f.ty.resolved.args.head)}");
        }
        
        case _ => {}//throw new AssertionError("Unreachable")
      }
    }
    return refs;
  }
}
