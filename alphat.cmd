IF [%1%]==[] goto runall

alphac testcases/%1.a testcases/%1.exe
start "" testcases/%1.exe
exit

:runall
FOR %%c in (testcases/*.a) DO (
	alphac testcases/%%c testcases/%%c.exe
	start "" testcases/%%c.exe
)