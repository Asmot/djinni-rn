package djinni
import djinni.syntax._
import java.io._
import scala.io.Source

import java.io.{File, BufferedReader, FileNotFoundException, InputStreamReader, FileInputStream, Writer}

import djinni.ast.Interface.Method
import djinni.ast.Record.DerivingType.DerivingType
import djinni.syntax._
import djinni.ast._
import java.util.{Map => JMap}
import org.yaml.snakeyaml.Yaml
import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.util.control.Breaks._
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.input.{Position, Positional}

package object utils {
    def normalizePath(path: File) : File = {
        return new File(java.nio.file.Paths.get(path.toString()).normalize().toString())
    }   

    def slurpReader(in: java.io.Reader): String = {
        var buf = new Array[Char](4 * 1024)
        var pos = 0
        while (true) {
            val space = buf.length - pos
            val read = in.read(buf, pos, space)
            if (read == -1) {
                val r = new Array[Char](pos)
                return new String(buf, 0, pos)
            }
            pos += read
            if (pos >= buf.length) {
                val newBuf = new Array[Char](buf.length * 2)
                System.arraycopy(buf, 0, newBuf, 0, pos)
                buf = newBuf
            }
        }
        throw new AssertionError("unreachable")  // stupid Scala
    }

    def readFileCon(path: String) : String = {
        val file = new File(path);
        return readFileCon(file);
    }

    def readFileCon(file: File) : String = {
        val normalizedFile = normalizePath(file);
        val fin = new FileInputStream(normalizedFile)
        try {
            return slurpReader(new InputStreamReader(fin, "UTF-8"))
        } finally {
            fin.close()
        }
    }


    // append str with \n
    def s_wl(str: String, info: String) : String = {
        return str + info + "\r\n"
    }

    // append str
    def s_w(str: String, info: String) : String = {
        return str + info
    }

}