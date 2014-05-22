package mdel.tmlpdx;
package interpreter;

import _root_.mdel.tmlpdx.poly._;
import scala.collection.immutable.Map;
import scala.collection.immutable.HashMap;

// * * * * * * * * * * * * * *
//
// abstract syntax terms
//
abstract class SyntaxTerm;

// unary operations
abstract class Uny;
case object NEGATE extends Uny;
case object NOT extends Uny;
case object PRINT extends Uny;
case object PRINTLN extends Uny;
case object HD extends Uny;
case object TL extends Uny;
case object ISNULL extends Uny;
case class SELECT(which:Int) extends Uny;

// binary operations  
abstract class Bny;
case object SEQ extends Bny
case object PLUS extends Bny;
case object MINUS extends Bny;
case object TIMES extends Bny;
case object DIV extends Bny;
case object MOD extends Bny;
case object AND extends Bny;
case object OR extends Bny;
case object EQUAL extends Bny;
case object UNEQUAL extends Bny;
case object LESS extends Bny;
case object LESSEQUAL extends Bny;
case object GREATER extends Bny;
case object GREATEREQUAL extends Bny;
case object PREPEND extends Bny;

// class CharStreamPosition
// -- location of a particular character in a CharStream.
//
case class CharStreamPosition(line:Int, column:Int) {
  //
  // CharStreamPosition((Int,Int))
  def this(position:(Int,Int)) { this(position._1,position._2) }  
  //
  // toString - converts a position intto text useful for reporting an error.
  override def toString:String = "[line "+line+", column "+column+"]"
  //
  // to - construct a CharStreamRegion from this to that.
  def to(that:CharStreamPosition):CharStreamRegion = new CharStreamRegion(this,that)
}

// class CharStreamRegion
// -- range of characters within a CharStream.
case class CharStreamRegion(start:CharStreamPosition, end:CharStreamPosition) {
  override def toString:String = "from "+start+" to "+end
} 


// expressions
abstract class Exp extends SyntaxTerm {
  var csr:CharStreamRegion = null;
}
case class LITERAL(vlu:Vlu) extends Exp;
case class BINARY(bop:Bny, left:Exp, right:Exp) extends Exp;
case class PAIROF(e1:Exp,e2:Exp) extends Exp;
case class IF(cnd:Exp, thn:Exp, els:Exp) extends Exp;
case class LET(dfn:Dfn, body:Exp) extends Exp;
case class NAME(name:String) extends Exp;  
case class APPLY(left:Exp,right:Exp) extends Exp;
case class FN(formal:String,rule:Exp) extends Exp;

// definitions
abstract class Dfn extends SyntaxTerm;
case class FUNDFN(defs:List[Tuple3[String,String,Exp]]) extends Dfn;
case class NAMEDFN(name:String,defn:Exp) extends Dfn;

//
// name->value binding environments
//
class Env(contents:Map[String,Vlu]) {
  def this() { this(new HashMap()) }
  def apply(key:String):Vlu = contents(key)
  def ::(assoc:Tuple2[String,Vlu]):Env = new Env(contents + assoc)
}

// values
abstract class Vlu;

case object UNIT extends Vlu { 
  override def toString:String = {
    "()"
  }
}

case class BOOL(valueOf:Boolean) extends Vlu { 
  override def toString:String = {
    valueOf.toString
  } 
}

case class INT(valueOf:Int) extends Vlu { 
  override def toString:String = {
    valueOf.toString
  }
}

case class STRING(text:String) extends Vlu { 
  override def toString:String = {
    "\""+text+"\""
  } 
}

case class LIST(valuesOf:List[Vlu]) extends Vlu {
  override def toString:String = {
    var s:String = "[";
    var first:Boolean = true;
    for (v <- valuesOf) {
      if (first) {
        s += v.toString; 
        first = false;
      } else {
        s += "," + v.toString; 
      }
    }
    s += "]"
    return s;
  }
}

case class PAIR(v1:Vlu,v2:Vlu) extends Vlu {
  override def toString:String = {
    return "("+v1.toString+","+v2.toString+")";
  }
}

case class CLOSURE(formal:String,rule:Exp,var context:Env) extends Vlu {
  override def toString:String = "fn"
}

case class PRIMITIVE(uny:Uny) extends Vlu {
  override def toString:String = "fn"
}

object interpreter {

  // * * * * * * * * * * * * * *
  //
  // interpreter
  //

  // 
  // extend : Env x Dfn -> Env
  //
  // Given an evaluation context, extends that context with names
  // provided by a definition.  If the definition is a NAMEDFN, then
  // a value is bound to that name.  If the definition is a FUNDFN, 
  // then a (curried) function value is bound to that function's 
  // name.  If it's a record OPENDFN, then a record is constructed
  // and then its field components are bound as names to the given
  // context (via the "unwrap" method).
  //
  def extend(env:Env,dfn:Dfn):Env = {
    dfn match {
      // 
      case NAMEDFN(nme,exp) => {
        //
        // evaluate the defining expression 
        val vlu:Vlu = eval(exp,env);
        //
        // add that name/value binding
        (nme,vlu)::env
      }
      case FUNDFN(defs) => {
        var envp:Env = env;
        // build a list of closures, each with a bogus context; build the context
        var clos:List[CLOSURE] = for ((name,param,rule) <- defs) yield { 
          val clo:CLOSURE = new CLOSURE(param,rule,null);
          envp = (name,clo)::envp;
          clo
        }
        // fix each closure so that it knows it and its fellow recursive functions
        for (clo <- clos) {
          clo.context = envp;
        }
        // give back the extended environment
        return envp;
      }
    }
  }
  
  // 
  // eval : Exp x Env -> Vlu
  //
  // Evaluate the given expression term in the provided evaluation
  // context.
  //
  def eval(exp:Exp,env:Env):Vlu = {
    exp match {
      case FN(formal,rule) => CLOSURE(formal,rule,env);
      case APPLY(fe,ae) => eval(fe,env) match {
        case PRIMITIVE(uop) => evalUop(uop,eval(ae,env));
        case CLOSURE(formal,rule,ctxt) => eval(rule,(formal,eval(ae,env))::ctxt)
      }
      case PAIROF(e1,e2) => PAIR(eval(e1,env),eval(e2,env))
      case LET(dfn,bdy) => eval(bdy,extend(env,dfn))
      case NAME(nme) => env(nme)
      case LITERAL(vlu) => vlu
      case IF(cnd,thn,els) => eval(cnd,env) match {
        case BOOL(true) => eval(thn,env)
        case BOOL(false) => eval(els,env)
      }
      case BINARY(_,_,_) => evalBop(exp,env)
    }

  }

  // evalUop: Exp x Env x Lib -> Vlu
  def evalUop(uop:Uny,arg:Vlu):Vlu = {
    (uop,arg) match {
      case (HD,LIST(v::_)) => v
      case (TL,LIST(_::vs)) => LIST(vs)
      case (SELECT(1),PAIR(v1,v2)) => v1
      case (SELECT(2),PAIR(v1,v2)) => v2
      case (ISNULL,LIST(Nil)) => BOOL(true)
      case (ISNULL,LIST(_)) => BOOL(false)
      case (NEGATE,INT(i)) => INT(-i)
      case (NOT,BOOL(b)) => BOOL(!b)        
      case (PRINT,v) => { print(v.toString); UNIT }
      case (PRINTLN,v) => { println(v.toString); UNIT }
    }
  }

  // evalBop : Exp x Env -> Vlu
  def evalBop(exp:Exp,env:Env):Vlu = {
    exp match {
      case BINARY(AND,lft,rgt) => 
        eval(lft,env) match {
          case BOOL(true) => eval(rgt,env)
          case BOOL(false) => BOOL(false)
        }
      case BINARY(OR,lft,rgt) => 
        eval(lft,env) match {
          case BOOL(false) => eval(rgt,env)
          case BOOL(true) => BOOL(true)
        }
      case BINARY(SEQ,lft,rgt) => {
        eval(lft,env);
        eval(rgt,env)
      }
      case BINARY(PREPEND,lft,rgt) => {
        val v:Vlu = eval(lft,env);
        eval(rgt,env) match {
          case LIST(vs) => LIST(v::vs)
        }
      }
      case BINARY(EQUAL,lft,rgt) => {
        (eval(lft,env),eval(rgt,env)) match {
          case (UNIT,UNIT) => BOOL(true)
          case (BOOL(b),BOOL(c)) => BOOL(b == c)
          case (INT(i),INT(j)) => BOOL(i == j)
          case (STRING(s),STRING(t)) => BOOL(s == t)
          case (LIST(xs),LIST(ys)) => BOOL(xs == ys)
          case (PAIR(x1,y1),PAIR(x2,y2)) => BOOL(x1==x2 && y1==y2)
        }
      }
      case BINARY(UNEQUAL,lft,rgt) => {
        (eval(lft,env),eval(rgt,env)) match {
          case (UNIT,UNIT) => BOOL(false)
          case (BOOL(b),BOOL(c)) => BOOL(b != c)
          case (INT(i),INT(j)) => BOOL(i != j)
          case (STRING(s),STRING(t)) => BOOL(s != t)
          case (LIST(xs),LIST(ys)) => BOOL(xs != ys)
          case (PAIR(x1,y1),PAIR(x2,y2)) => BOOL(x1!=x2 || y1!=y2)
        }
      }
      case BINARY(bop,lft,rgt) => {
        (eval(lft,env),eval(rgt,env)) match {
          case (INT(i),INT(j)) => 
            bop match {
              case PLUS =>  INT(i + j)
              case MINUS => INT(i - j)
              case TIMES => INT(i * j)
              case DIV =>   INT(i / j)
              case MOD =>   INT(i % j)
              case EQUAL =>   BOOL(i == j)
              case UNEQUAL => BOOL(i != j)
              case LESS =>         BOOL(i < j)
              case LESSEQUAL =>    BOOL(i <= j)
              case GREATER =>      BOOL(i > j)
              case GREATEREQUAL => BOOL(i >= j)
            }
          case (BOOL(b),BOOL(c)) => 
            bop match {
              case EQUAL =>   BOOL(b == c)
              case UNEQUAL => BOOL(b != c)
          } 
        }
      }
    }
  }

}
