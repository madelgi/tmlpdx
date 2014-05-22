# tmlPDX

A type inference engine for ML supporting int, boolean, function, pair, and list
types, and also let-bounded polymorphism. Much of the included code was provided by
[Jim Fix](http://www.people.reed.edu/~jimfix/).

## About

## Usage

In the main directory, type 'sbt compile' to compile the source code. Type 'sbt run'
to open the interactive ML interpreter. To load the interpreter with a .sml file, type
"sbt 'run <file.sml>'".

If you do not have sbt, the source files may be compiled directly in the following 
order:

1. poly.scala
2. interpreter.scala
3. checker.scala
4. parser.scala
5. tmlpdx.scala

Then, within the same directory, type 'scala mdel.tmlpdx.tmlpdx.tmlpdx' to run the 
interactive interpreter. To run with a .sml file, type 
'scala mdel.tmlpdx.tmlpdx.tmlpdx <file.sml>'
