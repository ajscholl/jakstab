#!/bin/bash
JSCLASSPATH=lib/antlr.jar:lib/google-collect-1.0.jar:lib/javabdd-1.0b2.jar:scala-library.jar:lib/bdd.jar:lib/scalacheck_2.10-1.11.1.jar
case `uname` in
    CYGWIN*)
        JSCLASSPATH=`cygpath -p -d "$JSCLASSPATH"`
        ;;
    *)
esac
if [ ! -d bin ]; then mkdir bin; fi
javac -d bin/ `find -L src/ -name '*.java'` -cp ${JSCLASSPATH}
