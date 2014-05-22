package mdel.tmlpdx;
package parser;

import _root_.mdel.tmlpdx.poly._;
import _root_.mdel.tmlpdx.interpreter._;
import _root_.mdel.tmlpdx.checker._;
import scala.collection.immutable.HashMap;
import scala.collection.mutable.Stack;

// class CharStream
// -- representation of a stream of characters, typically either program 
//    source from a file, or lines entered into an interactive shell.
abstract class CharStream {
  var line:Int = 1;
  var column:Int = 1;
  var lastpos:(Int,Int) = (0,0);
    
  def lastPosition(u:Unit):CharStreamPosition = new CharStreamPosition(lastpos)
  def position:CharStreamPosition = new CharStreamPosition(line,column)
  def resetPosition:Unit = { line = 1; column = 1; }
  def advance(u:Unit):Unit;
  def current(u:Unit):Char;
  def clear(u:Unit):Unit;
  def isAtWhiteSpace:Boolean = " \t\n\r" contains (current())
  def isAtEOF:Boolean = current() == '\000'
  def isAtAlpha:Boolean = (('a' to 'z') contains current()) || (('A' to 'Z') contains current())
  def isAtDigit:Boolean = ('0' to '9') contains (current())
  def isAtAlphaNumeric:Boolean = isAtDigit || isAtAlpha || current() == '_' 
  def isAtOpChar:Boolean = ".~!@#%^&|+-*/%:;<>=," contains current()
  def isAtDQuote:Boolean = current() == '\"'
  def isAtEscape:Boolean = current() == '\\';
  def advanceToNonWhiteSpace:Unit = while (isAtWhiteSpace) advance()
 
  def advanceEscape:Char = {
    updatePosition;
    advance();
    val c:Char = current();
    val nextc:Char = current() match {
      case '\\' => '\\';
      case 'n'  => '\n';
      case 't'  => '\t';
      case '\"' => '\"';
      case '\r' => '\r';
      case 'x' => {
  advance();
  val c0:Char = current(); advance();
  val c1:Char = current();
  (c0*16+c1).toChar
      }
      case _ if c >= 0 && c<8 => {
  val c0:Char = current(); advance();
  val c1:Char = current(); advance();
  val c2:Char = current();
  (c0*64 + c1*8 + c2).toChar
      }
    }
    advance();
    nextc
  }
      
  def updatePosition:Unit = {
    // save the place where the current() character sits
    lastpos = (line,column);

    // update line/column info accordingly
    if (current() == '\n') {
      line_= (line + 1);
      column_= (1);
    } else if (current() == '\t') {
      column_= (column + 4);
    } else {
      column_= (column + 1);
    }
     
  }
}

class CharStreamStdin extends CharStream {
  private var theCurrentLine:List[Char] = Nil;
  def clear(u:Unit):Unit = {
    theCurrentLine = Nil;
    resetPosition;
  }
  def getLineIfNecessary:Unit = {
    if (theCurrentLine == Nil) {
      val s:String = Console.readLine;
      if (s == null) {
  theCurrentLine = List('\000');
      } else {
        theCurrentLine = (s + "\n").toList;
      }
    }
  }
  def current(u:Unit):Char = { 
    getLineIfNecessary;
    return theCurrentLine.head;
  }
  def advance(u:Unit):Unit = {
    updatePosition;
    theCurrentLine = theCurrentLine.tail;
  }  
}

class CharStreamFull(source:String) extends CharStream {
  private var theWholeText = (source+"\000").toList
  def clear(u:Unit):Unit = {
    theWholeText = List('\000');
  }
  def current(u:Unit):Char = theWholeText.head
  def advance(u:Unit):Unit = {
    updatePosition;
    theWholeText = theWholeText.tail
  }  
}

class ParseException(m:String) extends ProcessException {
  val msg = m;
  def message = msg;
}

class TokenStream(stream:CharStream) {

  //
  // class Token
  //
  //
  // object classes for what's produced by a TokenStream
  //
  abstract class Token 
  //
  //
  // end-of-stream token
  //
  case object EofToken extends Token;
  //
  //
  // literals and identifiers
  //
  case class IntToken(value:Int) extends Token
  case class StringToken(text:String) extends Token
  case class IdToken(identifier:String) extends Token { def this() = { this("") } }
  //
  //
  // parenthesis-like tokens
  //
  case object LParenToken extends Token
  case object RParenToken extends Token
  case object LBraceToken extends Token
  case object RBraceToken extends Token
  case object LBrackToken extends Token
  case object RBrackToken extends Token
  //
  // superclass for all operator tokens
  //
  abstract class OpToken extends Token
  //
  
  //
  // character sets that differntiate the basic token types
  //
  val opSet = HashMap[String,Token]()
  val keySet = HashMap[String,Token]()
  val enclosureSet = HashMap[Char,Token]('('->LParenToken,')'->RParenToken,
           '{'->LBraceToken,'}'->RBraceToken,
           '['->LBrackToken,']'->RBrackToken)
  //
  // state of the TokenStream/CharStream engine
  //
  private var token:Token = null
  private var start:CharStreamPosition = null
  private var end:CharStreamPosition = null

  //
  // methods for advancing and accessing the head token
  //
  private def fillIfNecessary:Unit = {
     if (token == null) { 
        stream.advanceToNonWhiteSpace;
  start = stream.position;
  token = produceNextToken;
        end = stream.lastPosition()
     }
  }

  private val markings:Stack[CharStreamPosition] = new Stack[CharStreamPosition]();
  def mark:Unit = { markings.push(currentTokenStart); }
  def dupemark:Unit = { markings.push(markings.top); }
  def unmark:CharStreamRegion = { markings.pop() to currentTokenEnd; }
  def currentTokenStart:CharStreamPosition = { fillIfNecessary; start }
  def currentTokenEnd:CharStreamPosition = { fillIfNecessary; end }
  def currentTokenRegion:CharStreamRegion = { fillIfNecessary; start to end }
  def currentToken:Token = { fillIfNecessary; token }
  def error(msg:String) = {
    throw new ParseException("Error at "+(stream.position)+": "+msg);
  }
  def isAtEof:Boolean = { return currentToken == EofToken }
  def advance:Unit = { token = null; }
  def advanceTo(t:Token) { while (currentToken != t) { advance; } }
  def clearStream:Unit = {
    token = null;
    stream.clear();
  }

  def eatIdToken:String = {
    currentToken match {
      case IdToken(x) => advance; x
      case _ => error("Expected a name token. Got a "+currentToken+" instead.");
    }
  }

  def eat(t:Token):Unit = {
    if (t.hashCode == currentToken.hashCode) {
      advance
    } else {
      error("Found "+currentToken+" but expected "+t+".")
    }
  }

  private def produceNextToken:Token = {   
    if (stream.isAtEOF) {
      EofToken
    } else if (stream.isAtDigit) {
      produceIntToken
    } else if (stream.isAtAlpha) {
      produceWordToken
    } else if (stream.isAtOpChar) {
      produceOpToken
    } else if (stream.isAtDQuote) {
      produceStringToken
    } else if (enclosureSet.contains(stream.current())) {
      val c = stream.current();
      stream.advance();
      enclosureSet(c)
    } else {
      error("Unexpected character \'"+(stream.current())+"\' while parsing next token.");
    }
  }

  private def produceIntToken:Token = {
    var value = 0
    while (stream.isAtDigit) {
      value = (value*10) + ((stream.current())-'0');
      stream.advance()
    }
    IntToken(value)
  }

  private def produceStringToken:Token = {
    var text:String = ""
    stream.advance();
    while (!(stream.isAtDQuote)) {
      if (stream.isAtEscape) {
  text = text + stream.advanceEscape;
      } else {
  text = text + (stream.current());
  stream.advance();
      }
    }
    stream.advance();
    StringToken(text)
  }

  private def produceWordToken:Token = {
    var word = ""
    while (stream.isAtAlphaNumeric) {
      word = word + (stream.current());
      stream.advance()
    }
    if (keySet.contains(word)) {
      keySet(word)
    } else {
      IdToken(word)
    }
  }

  private def produceOpToken:Token = {
    var word = ""
    while (stream.isAtOpChar) {
      word = word + (stream.current());
      stream.advance();
    }
    if (opSet.contains(word)) {
      opSet(word)
    } else {
      error("Unexpected operator token "+word+".")
    }
  }
}

//
// class Parser
//
// Parser object for handling typed MiniML source code.
//
class Parser(cs:CharStream) extends TokenStream(cs) {
  val src:CharStream = cs;

  // * * * * * * * *

  // ...extends Token
  //
  // These define the Token case objects to be examined during parsing.
  //
  case object IfToken extends Token
  case object ThenToken extends Token
  case object ElseToken extends Token
  case object FnToken extends Token
  case object ToToken extends OpToken
  case object LetToken extends Token
  case object ValToken extends Token
  case object OpenToken extends Token
  case object FunToken extends Token
  case object AndToken extends Token
  case object InToken extends Token
  case object EndToken extends Token
  case object NilToken extends Token
  case object HdToken extends Token
  case object TlToken extends Token
  case object NullToken extends Token
  case object PrintToken extends Token
  case object PrintlnToken extends Token
  case object IntToStringToken extends Token
  case object BoolToStringToken extends Token
  case object PlusToken extends OpToken
  case object MinusToken extends OpToken
  case object NegToken extends OpToken
  case object HashToken extends OpToken
  case object TimesToken extends OpToken
  case object DivToken extends Token
  case object ModToken extends Token
  case object NotToken extends Token
  case object AndAlsoToken extends Token  
  case object OrElseToken extends Token  
  case object TrueToken extends Token  
  case object FalseToken extends Token  
  case object EqualToken extends OpToken
  case object LessToken extends OpToken
  case object GreaterToken extends OpToken
  case object LessEqualToken extends OpToken
  case object GreaterEqualToken extends OpToken
  case object UnequalToken extends OpToken
  case object SemiToken extends OpToken
  case object ConsToken extends OpToken
  case object CommaToken extends OpToken
  case object ColonToken extends OpToken
  case object ArrowToken extends OpToken
  case object ListToken extends Token
  case object UnitToken extends Token
  case object IntTyToken extends Token
  case object BoolToken extends Token
  case object StringTyToken extends Token

  // opSet, keySet
  // 
  // These define what Tokens correspond to what character sequences
  //
  override val opSet = HashMap[String,Token]("+"->PlusToken,
                                             "-"->MinusToken,
                                             "*"->TimesToken,
                                             "="->EqualToken,
                                             "<"->LessToken,
                                             ">"->GreaterToken,
                                             "<="->LessEqualToken,
                                             ">="->GreaterEqualToken,
                                             "<>"->UnequalToken,
                                             ";"->SemiToken,
                                             ","->CommaToken,
                                             "::"->ConsToken,
                                             ":"->ColonToken,
                                             "->"->ArrowToken,
                                             "=>"->ToToken,
                                             "~"->NegToken,
               "#"->HashToken);
  override val keySet = HashMap[String,Token]("div"->DivToken,
                "mod"->ModToken,
                "andalso"->AndAlsoToken,
                "orelse"->OrElseToken,
                "not"->NotToken,
                "fn"->FnToken,
                "let"->LetToken,
                "val"->ValToken,
                "open"->OpenToken,
                "fun"->FunToken,
                "and"->AndToken,
                "in"->InToken,
                "end"->EndToken,
                "nil" -> NilToken,
                "hd"->HdToken,
                "tl"->TlToken,
                "null"->NullToken,
                "if"->IfToken,
                "true"->TrueToken,
                "false"->FalseToken,
                "then"->ThenToken,
                "else"->ElseToken,
                "print"->PrintToken,
                "println"->PrintlnToken,
                "inttostring"->IntToStringToken,
                "booltostring"->BoolToStringToken,
                "list"->ListToken,
                "unit"->UnitToken,
                "int"->IntTyToken,
                "bool"->BoolToken,
                "string"->StringTyToken);


  def emit(exp:Exp, csr:CharStreamRegion):Exp = {
    exp.csr = csr;
    exp
  }

  // * * * * * * * *
  //
  // parse*
  //
  // These first few methods define the top-level parsing methods
  // for MiniML.
  //

  // parseTopLevel*
  //
  // Useful for an interactive interpreter, this will parse either
  // a single MiniML expression or a single MiniML declaration, 
  // followed by a semicolon, and not eat the remaining input.
  //
  def isAtDfn:Boolean = (currentToken == ValToken) || (currentToken == FunToken);

  def parseTopLevelExp:Exp = {
    val e = parseExp;
    eat(SemiToken);
    return e;
  }

  def parseTopLevelDfn:Dfn = {
    val d:Dfn = parseDfn;
    eat(SemiToken);
    return d;
  }

  // * * * * * * * *
  //
  // parse*
  //
  // These remaining methods all constitute the recursive descent
  // parser for MiniML.
  //

  // parseDfn
  //
  // Parses a value or function declaration
  //
  // Syntax handled is of the form
  //    
  //    <def> ::= val <name>:<type> = <exp> 
  //    <def> ::= fun <fundef>
  //    <fundef> ::= <name> <name> ... <name> = <exp> <andmore>
  //    <andmore> ::= e | <and> <fundef>
  //
  def parseDfn:Dfn = {
    currentToken match {
      case ValToken => {
        eat(ValToken);
        val x:String = eatIdToken;
        eat(EqualToken);
        val e:Exp = parseExp;
        NAMEDFN(x,e)
      }
      case FunToken => {
        eat(FunToken);
  var defs = (eatIdToken, eatIdToken, parseFun)::Nil;
  while (currentToken == AndToken) {
    eat(AndToken);
    defs = (eatIdToken, eatIdToken, parseFun)::defs;
  }
  FUNDFN(defs);
      }
      case _ => error("Expected VAL or FUN.");
    }
  }

  def parseFun:Exp = {
    if (currentToken == EqualToken) {
      eat(EqualToken);
      return parseExp;
    } else {
      val x:String = eatIdToken;
      return FN(x,parseFun);
    }
  }


  // parseExp 
  //
  // parses a MiniML expression
  def parseExp:Exp = parseIfOrFn

  // parseIfOrFn
  //
  // Parses a conditional or function expression
  // whose syntax is given by 
  //
  //    <exp> ::= if <exp> then <exp> else <exp>
  //    <exp> ::= fn <name> => <exp>
  //
  def parseIfOrFn:Exp = {
    currentToken match {
      case IfToken => {
        mark;
        eat(IfToken);
        val c = parseExp;
        eat(ThenToken);
        val t = parseExp;
        eat(ElseToken);
        val e = parseExp;
        emit(IF(c,t,e),unmark)
      }
      case FnToken => {
  mark;
  eat(FnToken);
  val x = eatIdToken;
  eat(ToToken);
  emit(FN(x,parseExp),unmark)
      }
      case _ => parseBinary
    }
  }

  def parseBinary:Exp = {
    parseCons;
  }

  // parseCons
  //
  // Parses an expression whose syntax is given by
  //
  //    <exp> ::=  <exp> :: ... :: <exp> 
  //
  def parseCons:Exp = {
    mark;
    var e = parseDisj;
    if (currentToken == ConsToken) {
      eat(ConsToken);
      emit(BINARY(PREPEND,e,parseCons),unmark);
    } else {
      unmark;
      e
    }
  }

  // parseDisj
  //
  // Parses a series of disjunctions
  //
  //    <exp> ::= <exp> orelse <exp> orelse ... orelse <exp>
  //
  // or maybe just a single expression.
  //
  def parseDisj:Exp = {
    var e = parseConj;
    while (currentToken == OrElseToken) {
      mark;
      eat(OrElseToken);
      e = emit(BINARY(OR,e,parseConj),unmark);
    }
    return e;
  }

  // parseConj
  //
  // Parses a series of conjunctions of the form
  //
  //    <exp> ::= <exp> andalso <exp> andalso ... andalso <exp>
  //
  // or maybe just a single expression.
  //
  def parseConj:Exp = {
    // <exp> ...
    var e = parseCmp;
    while (currentToken == AndAlsoToken) {
      // ... andalso <exp> ...
      mark;
      eat(AndAlsoToken);
      e = emit(BINARY(AND,e,parseCmp),unmark);
    }
    return e;
  }

  // parseCmp
  //
  // Parses a series of value comparisons of the form
  //
  //    <exp> ::= <exp> <op> <exp> <op> ... <op> <exp>
  //    <op> ::= <> | = | < | <= | >= | >
  //
  // or maybe just a single expression.
  //
  def parseCmp:Exp = {
    var e = parseSum;
    while (currentToken == LessToken || currentToken == GreaterToken || currentToken == LessEqualToken
           || currentToken == GreaterEqualToken || currentToken == EqualToken || currentToken == UnequalToken) {
      mark; currentToken match {
        case LessToken => { eat(LessToken); e = emit(BINARY(LESS,e,parseSum),unmark); }
        case GreaterToken => { eat(GreaterToken); e = emit(BINARY(GREATER,e,parseSum),unmark); }
        case LessEqualToken => { eat(LessEqualToken); e = emit(BINARY(LESSEQUAL,e,parseSum),unmark); }
        case GreaterEqualToken => { eat(GreaterEqualToken); e = emit(BINARY(GREATEREQUAL,e,parseSum),unmark); }
        case EqualToken => { eat(EqualToken); e = emit(BINARY(EQUAL,e,parseSum),unmark); }
        case UnequalToken => { eat(UnequalToken); e = emit(BINARY(UNEQUAL,e,parseSum),unmark); }
      }
    }
    return e;
  }

  // parseSum
  //
  // Parses a series of additions and subtractions of the form
  //
  //    <exp> ::= <exp> <op> <exp> <op> ... <op> <exp>
  //    <op> ::= + | -
  //
  // or maybe just a single expression.
  //
  def parseSum:Exp = {
    var e = parseProd;
    while (currentToken == PlusToken || currentToken == MinusToken) {
      mark; currentToken match {
        case PlusToken => { eat(PlusToken); e = emit(BINARY(PLUS,e,parseProd),unmark); }
        case MinusToken => { eat(MinusToken); e = emit(BINARY(MINUS,e,parseProd),unmark); }
      }
    }
    return e;
  }

  // parseProd
  //
  // Parses a series of multiplication and division operations expressed
  // as
  //
  //    <exp> ::= <exp> <op> <exp> <op> ... <op> <exp>
  //    <op> ::= * | div | mod
  //
  // or maybe just a single expression.
  //
  def parseProd:Exp = {
    var e = parseApp;
    while (currentToken == TimesToken || currentToken == DivToken || currentToken == ModToken) {
      mark; currentToken match {        
        case TimesToken => { eat(TimesToken); e = emit(BINARY(TIMES,e,parseApp),unmark); }
        case DivToken =>   { eat(DivToken); e = emit(BINARY(DIV,e,parseApp),unmark); }
        case ModToken =>   { eat(ModToken); e = emit(BINARY(MOD,e,parseApp),unmark); }
      }
    }
    return e;
  }

  val appStops:List[Token] = List(RParenToken, RBrackToken, RBraceToken,
          EofToken, 
          SemiToken, CommaToken,
          ThenToken, ElseToken, EndToken, InToken, 
          EqualToken, UnequalToken, 
          LessToken, LessEqualToken,
          GreaterToken, GreaterEqualToken,
          PlusToken, MinusToken, TimesToken,
          DivToken, ModToken, ConsToken,
          AndAlsoToken, OrElseToken,
          ValToken, FunToken, AndToken);  

  def parseApp: Exp = {
    mark
    var e:Exp = parseAtom;
    while (!appStops.contains(currentToken)) {
      dupemark;
      e = emit(APPLY(e,parseAtom),unmark);
    }
    unmark;
    return e;
  }

  // parseAtom
  //
  // Parses a literal value, a parenthesized expression, or a LET
  // expression.
  //
  // <atom> ::= ~ | not | print | println | hd | tl | 
  // <atom> ::= <name> | <int> | true | false | () | <string> | nil
  // <atom> ::= let <def> in <exp> end
  // <atom> ::= ( <exp> )
  // <atom> ::= ( <exp>; ... ; <exp> )
  //
  def parseAtom:Exp = {
    currentToken match {
      case HashToken => { mark; advance; currentToken match {
  case IntToken(i) => { advance; emit(LITERAL(PRIMITIVE(SELECT(i))),unmark); }
  case _ => error("Unexpected field select of "+currentToken+".");
      }
           }
      case NegToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(NEGATE)),unmark); }
      case NotToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(NOT)),unmark); }
      case PrintToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(PRINT)),unmark); }
      case PrintlnToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(PRINTLN)),unmark); }
      case HdToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(HD)),unmark); }
      case TlToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(TL)),unmark); }
      case NullToken =>      { mark; advance; emit(LITERAL(PRIMITIVE(ISNULL)),unmark); }
      case NilToken =>       { mark; eat(NilToken); return emit(LITERAL(LIST(Nil)),unmark); }
      case IdToken(x) =>     { mark; advance; return emit(NAME(x),unmark); }
      case IntToken(n) =>    { mark; advance; return emit(LITERAL(INT(n)),unmark); }
      case StringToken(s) => { mark; advance; return emit(LITERAL(STRING(s)),unmark); }
      case TrueToken =>      { mark; eat(TrueToken); return emit(LITERAL(BOOL(true)),unmark); }
      case FalseToken =>     { mark; eat(FalseToken);return emit(LITERAL(BOOL(false)),unmark); }
      case LParenToken =>    parseParen
      case LBrackToken =>    parseList
      case LetToken =>       parseLet
      case _ => error("Unexpected token of "+currentToken+".");
    }
  }

  // parseLet
  //
  // Parses expressions of the form
  //
  //   <exp> ::= let <defs> in <exp> end
  //   <defs> ::= <def> <defs> | <def>
  //
  def parseLet:Exp = {
    mark
    eat(LetToken);
    parseLetP(parseDfn)
  }

  // parseLetP
  // 
  // Helper function for parseLet that creates a
  // series of nested LET terms, one for each 
  // definition it parses.
  //
  def parseLetP(d:Dfn):Exp = {
    if (currentToken == InToken) {
      eat(InToken);
      val b = parseSeq(parseExp);
      eat(EndToken);
      emit(LET(d,b),unmark)
    } else {
      mark
      emit(LET(d,parseLetP(parseDfn)),unmark);
    }
  }

  // parseList
  //
  // Parses a list of values.
  //
  def parseList:Exp = {
    eat(LBrackToken);
    if (currentToken == RBrackToken) {
      mark;
      eat(RBrackToken);
      return emit(LITERAL(LIST(Nil)),unmark);
    } else {
      val l:Exp = parseListItems;
      eat(RBrackToken);
      return l;
    }
  }
  def parseListItems:Exp = {
    mark;
    val e:Exp = parseExp;
    if (currentToken == CommaToken) {
      eat(CommaToken);
      return emit(BINARY(PREPEND,e,parseListItems),unmark);
    } else {
      return emit(BINARY(PREPEND,e,LITERAL(LIST(Nil))),unmark);
    }
  }
  

  // parseParen
  //
  // Parses a list of values.
  //
  def parseParen:Exp = {
    eat(LParenToken);
    mark
    if (currentToken == RParenToken) {
      eat(RParenToken);
      return emit(LITERAL(UNIT),unmark);
    } else {
      val e:Exp = parseExp;
      currentToken match {
        case RParenToken => {        
    unmark;
          eat(RParenToken);
          return e;
        }
        case SemiToken => {
    unmark;
          val es:Exp = parseSeq(e)
          eat(RParenToken);
          return es;
        }
        case CommaToken => {
    eat(CommaToken);
          val ep = parseExp;
          eat(RParenToken);
          return emit(PAIROF(e,ep),unmark);
        }
      }
    }
  }

  // parseSeq
  //
  // This parses a series of expressions separated by semicolons in
  // order to build a sequence expressions term.
  //
  def parseSeq(f:Exp):Exp = {
    var e:Exp = f;
    while (currentToken == SemiToken) {
      mark
      eat(SemiToken);
      e = emit(BINARY(SEQ,e,parseExp),unmark);
    }
    return e;
  }

  // parseTuple
  //
  // This parses a series of expressions separated by commas in
  // order to build a tuple term.
  //
  def parseTuple:List[Exp] = {
    if (currentToken == CommaToken) {
      eat(CommaToken);
      return parseExp::parseTuple;
    } else {
      return Nil;
    }
  }
}
