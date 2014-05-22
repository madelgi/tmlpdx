package mdel.tmlpdx;
package tmlpdx;

import _root_.mdel.tmlpdx.poly._;
import _root_.mdel.tmlpdx.interpreter._;
import _root_.mdel.tmlpdx.checker._;
import _root_.mdel.tmlpdx.parser._;
import scala.io.{BufferedSource,Source};
import scala.collection.mutable.Stack; 
import scala.collection.immutable.Map;
import scala.collection.immutable.HashMap;
import java.io.File;

object tmlpdx {

  def imprt(files:Array[String]):(Env,TyCtxt) = {
    var env = new Env();
    var ctxt = new TyCtxt();

    // 
    // import definitions from any of the command-line-specified MiniML source files
    //
    for (f <- files) {

      // open the source file
      println("[opening "+f+"]");
      try {
        val source = scala.io.Source.fromFile(f);
        val parser:Parser = new Parser(new CharStreamFull(source.mkString));
        source.close();
  try {
          // read each definition from the source file
          while (!parser.isAtEof) {
            val dfn:Dfn = parser.parseDfn;
      ctxt = checker.check(ctxt,dfn);
      env = interpreter.extend(env,dfn);
          } 
  } catch {
          case e:ProcessException => {
            e.report
          }
  }
      } catch {
  case e:Exception => {
    println(e);
  }
      }
    }
    return (env,ctxt);
  }

  def main(args:Array[String]):Unit = {

    val classFile:File = new File("tmlpdx.class");
    println("Reed College MATH 384 MiniML of PDX v2014.7 [built: "+new java.util.Date(classFile.lastModified())+"]");

    //
    // initialize the top-level environment
    //
    val et:(Env,TyCtxt) = imprt(args);
    var topLevelEnv = et._1;
    var topLevelCtxt = et._2;

    //
    // interactive READ-EVAL-PRINT loop
    //
    print("- ");
    val cs:CharStream = new CharStreamStdin();
    while (!cs.isAtEOF) {
      try {
  val parser:Parser = new Parser(cs);

        // ***************
        // READ-EVAL-PRINT
  
  if (!parser.isAtEof){ 
          val dfn:Dfn = if (parser.isAtDfn) {
            // read a definition
            parser.parseTopLevelDfn;
          } else {
            // read an expression, make an "it" definition
            val exp:Exp = parser.parseTopLevelExp;
            NAMEDFN("it",exp);
          }

    topLevelCtxt = checker.check(topLevelCtxt,dfn);
    topLevelEnv = interpreter.extend(topLevelEnv,dfn);
          reportDfn(dfn,topLevelEnv,topLevelCtxt);
    
          //
          // ***************
  }
      } catch {
  case e:CheckException => {
    e.report
  }
  case e:ParseException => {
    cs.clear();
          e.report
  }
  case e:EvaluateException => {
    e.report
  }
  case e:ProcessException => {
          e.report
  }
      }
      
      print("- ");
    }
  }

  def reportDfn(dfn:Dfn,env:Env,ctxt:TyCtxt):Unit = {
    dfn match {
      case NAMEDFN(x,_) => {
  println("val "+x+" = " + env(x) + " : " + ctxt(x));
      }
      case FUNDFN(fs) => {
  for ((f,_,_) <- fs) {
    println("val "+f+" = fn" + " : " + ctxt(f));
  }
      }
    }
  }

}
