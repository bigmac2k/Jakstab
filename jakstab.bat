@echo off
set JS_HOME=%~dp0
java -Xms512m -Xmx1000m -ea -cp "%JS_HOME%lib\antlr.jar;%JS_HOME%lib\google-collect-1.0.jar;%JS_HOME%lib\javabdd-1.0b2.jar;%JS_HOME%lib\bdd.jar;%JS_HOME%scala-library.jar;%JS_HOME%bin" org.jakstab.Main %*
