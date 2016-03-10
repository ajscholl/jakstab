#!/bin/bash
JSCLASSPATH=lib/antlr.jar:lib/google-collect-1.0.jar:lib/javabdd-1.0b2.jar:scala-library.jar:lib/bdd.jar:lib/scalacheck_2.10-1.11.1.jar
case `uname` in
    CYGWIN*)
        JSCLASSPATH=`cygpath -p -d "$JSCLASSPATH"`
        ;;
    *)
esac
mkdir -p bin
#javac -d bin/ `find -L src/ -name '*.java'` -cp ${JSCLASSPATH}
TODO=`make all`
DONE=1
for i in $TODO
do
    echo Compiling $i
    DONE=0
done
if [[ $DONE -eq 0 ]]
then
    echo javac -d bin/ $TODO -cp bin/:${JSCLASSPATH} > __docompile.sh
    sh __docompile.sh
    rm __docompile.sh
fi

