@echo off
IF NOT EXIST bin mkdir bin
javac -sourcepath src\ -cp lib\antlr.jar;lib\google-collect-1.0.jar;scala-library.jar;lib\javabdd-1.0b2.jar;lib\bdd.jar;lib/scalacheck_2.10-1.11.1.jar -d bin\ src\org\jakstab\*.java %*