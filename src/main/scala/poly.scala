//
// Type system support
//

package mdel.tmlpdx;
package poly;

import scala.collection.immutable.HashMap;

// * * * * * * * *  * * * * * * * *  * * * * * * * *  * * * * * * * * 
//   TYPE SYSTEM DEFINITIONS
// * * * * * * * *  * * * * * * * *  * * * * * * * *  * * * * * * * * 

//
// class Type - defined type terms
//
abstract class Type {
  def varsOf:List[Int] = List();
  def hasOccurrenceOf(v:VARt):Boolean = this.varsOf.contains(v.id);
}
//
// the list type
//
// <typ> ::= <typ> list
//
case class LISTt(elt:Type) extends Type {
  override def toString:String = "("+elt+" list)";
  override def varsOf:List[Int] = elt.varsOf;
}
//
// the pair type
//
// <typ> ::= <typ> * <typ>
//
case class PAIRt(t1:Type,t2:Type) extends Type {
  override def toString:String = "("+ t1 + " * " + t2 +")";
  override def varsOf:List[Int] = t1.varsOf++t2.varsOf;
}
//
// the int type, the type of integers
//
// <typ> ::= int
//
case object INTt extends Type {
  override def toString:String = "int";
}
//
// the unit type, return type of the Print expression
//
// <typ> ::= unit
//
case object UNITt extends Type {
  override def toString:String = "unit";
}
//
// the boolean type
//
// <typ> ::= boolean
//
case object BOOLt extends Type {
  override def toString:String = "boolean";
}
//
// the arrow type, the type of functions
//
// <typ> ::= <typ> -> <typ>
//
case class ARROWt(from:Type,to:Type) extends Type {
  override def toString:String = "(" + from + " -> " + to + ")";
  override def varsOf:List[Int] = from.varsOf ++ to.varsOf;
}
//
// the forall type, the type of polymorhic let-bound names
//
// This type is an internal representation of polymorhic types
// as managed by the H-M inference algorithm.  It can be viewed
// as a factory of type instances, produced when the algorithm
// encounters use of a let-bound name within an expression.
//
// They are produced when "LET(FUN(..)..)" is checked, using
// the code checker.generalize; they are called to task (well, 
// instantiated) when "LOOKUP" is checked, producing a specifiable
// type term (with type variables that can be specified during
// unification) using the code checker.instantiate.
//
//
case class FORALLt(vars:List[Int],term:Type) extends Type {
  override def toString:String = {
    Poly.FORALLNAMES = new HashMap()
    var name:Int = 0;
    for (v <- vars) {
      Poly.FORALLNAMES += (v -> Poly.varNameFor(name));
      name = name + 1;
    }
    val s:String = term.toString;
    Poly.FORALLNAMES = null;
    return s;
  }
}
//
// the polymorphic variable type, a type term that can be bound to other type terms
// during unification
//
case class VARt(id:Int,var binding:Option[Type]) extends Type {
  def this() = this(Poly.fresh,None);
  override def equals(any:Any):Boolean = any match {
    case (a:VARt) => a.id == this.id
    case _ => false
  }
  override def toString:String = binding match {
    case None => if (Poly.FORALLNAMES == null) "'a_" + id else Poly.FORALLNAMES(id);
    case Some(t) => t.toString;
  }
  override def varsOf:List[Int] = binding match {
    case None => return List(id);
    case Some(t) => return t.varsOf;
  }
  def bindTo(t:Type) = {
    binding = Some(t);
  }
}


//
// name->type contexts
//
class TyCtxt(contents:Map[String,Type]) {
  def this() { this(new HashMap()) }
  def apply(key:String):Type = contents(key)
  def ::(assoc:Tuple2[String,Type]):TyCtxt = new TyCtxt(contents + assoc)
}


// * * * * * * * *
//
// module Type
//
// Contains all the code that supports Hindley-Milner type inference
// with let-bounded polymorphism.
//
object Poly {
  
  //
  //
  // used for generating fresh type variable names
  //
  var fresh_counter:Int = 0;
  //
  def fresh:Int = {
    fresh_counter = fresh_counter + 1;
    return fresh_counter;
  }
  
  //
  //
  // used for printing polymorphic type terms
  //
  var FORALLNAMES:Map[Int,String] = null;
  //
  def varNameFor(id:Int):String = {
    var s:String = "'";
    if (id == 0) {
      return "'a";
    } else {
      var i = id;
      while (i > 0) {
        val c:Char = ('a'+(i % 26)).toChar;
        s += c.toString;
        i = i/26;
      }
      return s;
    }
  }
}

