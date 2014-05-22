package mdel.tmlpdx;
package checker;

import _root_.mdel.tmlpdx.poly._;
import _root_.mdel.tmlpdx.interpreter._;
import scala.collection.immutable.Map;
import scala.collection.immutable.HashMap;
import java.io.File;
import scala.io.{BufferedSource,Source};

// * * * * * * * * * * * * * *
//
// interpreter support structures
//

//
// top-level type of source code process errors
//
abstract class ProcessException extends Exception {
  def message:String;
  def report:Unit = { println(message); }
}

// error handling
class EvaluateException(m:String,e:Exp) extends ProcessException {
  def message = { m + " (" + e.csr + ")" };
}

// error handling
class CheckException(m:String,e:Exp) extends ProcessException {
  def message = { m + " (" + e.csr + ")" };
}

object checker {

  //
  // unify -- attempt to equate two type terms
  //
  // Given two type terms, possibly with unbound type variables,
  // find any necessary variable substitutions (perform variable
  // bindings) to make the terms the same.
  //
  // The third parameter, e:Exp, is the expression that is being
  // checked by the system, and is provided only for reporting type
  // mismatch errors.
  //
  def unify(t1:Type,t2:Type,e:Exp):Unit = {
    (t1,t2) match {
      case (v1:VARt,v2:VARt) => {
        //
        // If they're both type variables...
        //
        (v1.binding,v2.binding) match {
          // check if they're bound.
      
          // If neither are bound and
          case (None,None) => 
            if (v1.id == v2.id) {
              // same variable name?  No need to act.
              return;
            } else {
              // differ? Then bind one to the other.
              v1.bindTo(v2);
              return;
            }

          // If either or both are bound, then recursively unify the
          // substitution terms.
          case (None,Some(b)) => { unify(t1,b,e); return; }
          case (Some(b),None) => { unify(b,t2,e); return; }
          case (Some(b1),Some(b2)) => { unify(b1,b2,e); return; }
        }
      }

      // If one's a type variable...
      //
      case (v:VARt,_) => {

        (v.binding) match {
          case None => {
            // ...and unbound then see if we can bind it,
            if (!t2.hasOccurrenceOf(v)) {
              v.bindTo(t2);
              return;
            }
          } 
          // otherwise recursively unify its substitution.
          case Some(t) => {
            unify(t,t2,e);
            return;
          }
        }
      }

      // (Same logic here as just above.)
      // 
      case (_,v:VARt) => {
        (v.binding) match {
          case None => {
            if (!t1.hasOccurrenceOf(v)) {
              v.bindTo(t1);
              return;
            }
          }
          case Some(t) => {
            unify(t1,t,e);
            return;
          }
        }
      }

      // Otherwise, the type term constructors must match up and
      // we need to (perhaps) recursively unify.
      //
      case (UNITt,UNITt)  => { return; }
      case (INTt,INTt)    => { return; }
      case (BOOLt,BOOLt)  => { return; }
      case (ARROWt(a1,r1),ARROWt(a2,r2)) => {
        unify(a1,a2,e);
        unify(r1,r2,e);
        return;
      }
      case (PAIRt(f1,s1),PAIRt(f2,s2)) => {
        // Change
        unify(f1,f2,e);
        unify(s1,s2,e);
        return;
      }
      case (LISTt(e1),LISTt(e2)) => {
        // Change
        unify(e1,e2,e);
        return;
      }
      case _ => {}
    }

    //
    // The type terms failed to unify;  report an error.
    //
    throw new CheckException("Type mismatch:\nExpected: "+t1+"\nSaw     : "+t2+"\n",e)
  }

  // replicateWith(tt,hm)
  // 
  // Replaces all occurrences of variables with a fresh 
  // collection of variables. The replacments are given by 
  // the map hm.
  //
  def replicateWith(tt:Type,hm:Map[Int,VARt]):Type = {
    tt match {
      case vt:VARt => (vt.binding) match {
        case None => hm(vt.id)
        case Some(vb) => replicateWith(vb,hm)
      }
      case UNITt => UNITt
      case INTt => INTt
      case BOOLt => BOOLt
      case ARROWt(ta,tr) => ARROWt(replicateWith(ta,hm),replicateWith(tr,hm))
      case PAIRt(tf,ts) => PAIRt(replicateWith(tf,hm),replicateWith(ts,hm))
      case LISTt(te) => LISTt(replicateWith(te,hm))
      case FORALLt(_,_) => throw new CheckException("Nested forall type not allowed.",LITERAL(UNIT));
    }
  }

  // generalize(t)
  //
  // Take a type term t with free variables vl = a1, a2, ... ak
  // and make a type polymorphic term FORALL a1...ak. t
  // Relies on replicateWith, written above.
  def generalize(t:Type):Type = {
    val vars:List[Int] = t.varsOf;
    var hm:Map[Int,VARt] = new HashMap[Int,VARt]();
    var vl:List[Int] = List();
    for (vi <- vars.reverse) {
      val vv = new VARt();
      hm = hm+(vi->vv);
      vl = vv.id::vl;
    }
    return FORALLt(vl,replicateWith(t,hm));
  }

  // instantiate(t) 
  //
  // If t is a FORALL type, builds a fresh type term
  // with all the forall parameters replaced by fresh
  // vars.  Relies on replicateWith, written above.
  //
  def instantiate(t:Type):Type = {
    t match {
      case FORALLt(vars,fat) => {
        var hm:Map[Int,VARt] = new HashMap[Int,VARt]();
        for (vi <- vars) {
          hm = hm+(vi->new VARt());
        }
        return replicateWith(fat,hm);
      }
      case _ => return t;
    }
  }
  
  // check
  //
  // This is the definition term analog for infer.
  // It builds a type term corresponding to the 
  // name defined by the Defn term.  One difference
  // is that it gives back, potentially, a polymorphic
  // type.  This provides "let bound" polymorphism.
  //
  def check(G:TyCtxt,dfn:Dfn):TyCtxt = {
    //
    // [f:t]G |- fn x=>r : t  [f:forall t]G |- b : t'
    // ----------------------------------------------
    // G |- let fun f x = r in b end : t'
    //
    dfn match {
      case FUNDFN(ds) => {
        val ftds = for ((f,x,r) <- ds) yield { 
          val fd = FN(x,r);
          fd.csr = r.csr;
          (f,new VARt(),fd) 
        }
        var Gp = G; 
        for ((f,tf,d) <- ftds) { 
          Gp = (f,tf)::Gp;
        }
        for ((f,tf,d) <- ftds) {
          val td = infer(Gp,d);
          unify(tf,td,d);
        }
        var Gpp = G; 
        for ((f,tf,d) <- ftds) { 
          Gpp = (f,generalize(tf))::Gpp;
        }
        return Gpp;
      }
      //      
      // G |- d : t  G[x:forall t] |- b : t'
      // -----------------------------------
      // G |- let val x=d in b end : t'
      //
      case NAMEDFN(x,d) => {
        val td = infer(G,d);
        return (x,generalize(td))::G;
      }
    }
  }

  //
  // infer - find the type of an expression within a given name->type
  //         context.
  // 
  // Uses H-M type inference to find the most general type of expression
  // e, with types of let-bound names specified by G.
  //
  def infer(G:TyCtxt,e:Exp):Type = {

    e match {

      // ******* LITERAL VALUES *******

      //
      //  --------------
      //  G |- () : unit
      //
      case LITERAL(UNIT) => UNITt;
      //
      //  ------------
      //  G |- n : int
      //
      case LITERAL(INT(_)) => INTt;
      //
      //  ----------------
      //  G |- true : bool
      //
      case LITERAL(BOOL(_)) =>   BOOLt;


      // ******* PRIMITIVE FUNCTIONS (UNARY OPERATIONS) ********

      //
      //  ------------------
      //  G |- nil : 'a list
      //
      case LITERAL(LIST(Nil)) => LISTt(new VARt());
      //
      //  -------------------
      //  G |- ~ : int -> int
      //
      case LITERAL(PRIMITIVE(NEGATE)) => ARROWt(INTt,INTt)
      //
      //  -----------------------
      //  G |- not : bool -> bool
      //
      case LITERAL(PRIMITIVE(NOT)) => ARROWt(BOOLt,BOOLt)
      //
      //  -----------------------
      //  G |- print : 'a -> unit
      //
      case LITERAL(PRIMITIVE(PRINT)) => ARROWt(new VARt(),UNITt)
      case LITERAL(PRIMITIVE(PRINTLN)) => ARROWt(new VARt(),UNITt)
      //
      //  ---------------------------
      //  G |- null : 'a list -> bool
      //
      case LITERAL(PRIMITIVE(ISNULL)) => ARROWt(LISTt(new VARt()),BOOLt)
      //
      //  -----------------------
      //  G |- hd : 'a list -> 'a
      //
      case LITERAL(PRIMITIVE(HD)) => {
        val a = new VARt();
        ARROWt(LISTt(a),a);
      }
      //
      //  ----------------------------
      //  G |- tl : 'a list -> 'a list
      //
      case LITERAL(PRIMITIVE(TL)) => {
        // Change
        val a = new VARt();
        ARROWt(LISTt(a),LISTt(a));
      }
      //
      //  -----------------------
      //  G |- #1 : 'a * 'b -> 'a
      //
      case LITERAL(PRIMITIVE(SELECT(1))) => {
        val a = new VARt();
        val b = new VARt();
        ARROWt(PAIRt(a,b),a);
      }
      //
      //  -----------------------
      //  G |- #2 : 'a * 'b -> 'b
      //
      case LITERAL(PRIMITIVE(SELECT(2))) => {
        // Change
        val a = new VARt();
        val b = new VARt();
        ARROWt(PAIRt(a,b),b);
      }


      //
      // -------------
      // G |- x : G(x) with fresh type variables
      //
      case NAME(x) => instantiate(G(x))


      //
      //  G |- e1 : int  G |- e2 : int
      //  ----------------------------
      //  G |- e1 + e2 : int
      //
      case BINARY(PLUS,e1,e2)   => arithInfer(G,List(e1,e2));
      case BINARY(MINUS,e1,e2)  => arithInfer(G,List(e1,e2));
      case BINARY(TIMES,e1,e2)  => arithInfer(G,List(e1,e2));
      case BINARY(DIV,e1,e2)    => arithInfer(G,List(e1,e2));
      case BINARY(MOD,e1,e2)    => arithInfer(G,List(e1,e2));
      //
      //  G |- e1 : t  G |- e2 : t
      //  ------------------------
      //  G |- e1 = e2 : bool
      //
      case BINARY(EQUAL,e1,e2)    => equalInfer(G,e1,e2);
      case BINARY(UNEQUAL,e1,e2)  => equalInfer(G,e1,e2);

      //
      //  G |- e1 : int  G |- e2 : int
      //  ----------------------------
      //  G |- e1 < e2 : bool
      //
      case BINARY(LESS,e1,e2)         => compareInfer(G,List(e1,e2));
      case BINARY(GREATER,e1,e2)      => compareInfer(G,List(e1,e2));
      case BINARY(LESSEQUAL,e1,e2)    => compareInfer(G,List(e1,e2));
      case BINARY(GREATEREQUAL,e1,e2) => compareInfer(G,List(e1,e2));
      //
      //  G |- e1 : bool  G |- e2 : bool
      //  ------------------------------
      //  G |- e1 andalso e2 : bool
      //
      case BINARY(AND,e1,e2)  => logicInfer(G,List(e1,e2));
      case BINARY(OR,e1,e2)   => logicInfer(G,List(e1,e2));
      //
      //  G |- e1 : t1  G |- e2 : t2
      //  --------------------------
      //  G |- e1 ; e2 : t2
      //
      case BINARY(SEQ,e1,e2) => {
        infer(G,e1);
        infer(G,e2);
      }

      //
      //  G |- c : bool  G |- t : s  G |- e : s
      //  -------------------------------------
      //  G |- if c then t else e : s
      //
      case IF(c,t,e) => {
        val tc = infer(G,c);
        unify(tc,BOOLt,c);
        val tt = infer(G,t);
        val te = infer(G,e);
        unify(tt,te,e);
        return tt;
      }

      //
      // See the code for CHECK
      //
      case LET(dfn,b) => {
        val Gp = check(G,dfn);
        val tb = infer(Gp,b);
        return tb;
      }

      //      
      // [x:s]G |- b : t
      // -----------------------
      // G |- fn x => r : s -> t
      //
      case FN(x,r) => {
        val tx = new VARt();
        val tr = infer((x,tx)::G,r);
        return ARROWt(tx,tr);
      }

      //
      // G |- f : s -> t  G |- a : s
      // ---------------------------
      // G |- f a : t
      //
      case APPLY(f,a) => {
        val tf = infer(G,f);
        val ta = infer(G,a);
        val tr = new VARt(); 
        unify(tf,ARROWt(ta,tr),f);
        return tr;
      }

      //
      // G |- e1 : t  G |- e2 : t list
      // -----------------------------
      // G |- e1 :: e2 : t list
      //
      case BINARY(PREPEND,eh,et) => {
        // Change
        val a1 = infer(G,eh);
        val a2 = infer(G,et);
        unify(a2,LISTt(a1),eh);
        return a2;
      }

      //
      // G |- e1 : t1  G |- e2 : t2
      // --------------------------
      // G |- (e1,e2) : t1 * t2  
      //
      case PAIROF(e1,e2) => {
        // Change
        val a1 = infer(G,e1);
        val a2 = infer(G,e2);
        return PAIRt(a1,a2);
      }

    }
  }

  def arithInfer(G:TyCtxt,es:List[Exp]):Type = {
    for (e <- es) {
      val t = infer(G,e);
      unify(t,INTt,e);
    }
    return INTt;
  }

  def equalInfer(G:TyCtxt,e1:Exp,e2:Exp):Type = {
    val t1:Type = infer(G,e1);
    val t2:Type = infer(G,e2);
    unify(t1,t2,e2);
    return BOOLt;
  }

  def compareInfer(G:TyCtxt,es:List[Exp]):Type = {
    for (e <- es) {
      val t = infer(G,e);
      unify(t,INTt,e);
    }
    return BOOLt;
  }

  def logicInfer(G:TyCtxt,es:List[Exp]):Type = {
    for (e <- es) {
      val t = infer(G,e);
      unify(t,BOOLt,e);
    }
    return BOOLt;
  }
}
