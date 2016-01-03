@echo off
set in=%1
set out=%2
set asm=%in:~0,-2%.asm
set obj=%in:~0,-2%.obj

IF [%3%]==[] goto defaultlib
set lib=%3
goto build
:defaultlib
set lib="C:/Alpha/lib"
:build
alpha.exe %in% %asm% %lib%
if ERRORLEVEL 1 goto :eof
ml /Fo %obj% %asm% /c

link %obj% %lib%/lib.lib /subsystem:console /entry:alphamain /out:%out%