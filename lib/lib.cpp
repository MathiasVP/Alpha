#define WIN32_LEAN_AND_MEAN
#include <Windows.h>
//TODO: Need to do experiments to
//find the correct size, and if dynamic resize can be needed
#define GC_HANDLER_LIST_SIZE 32768
#define GC_HEAP_SIZE 500000000

long gc_handlers[GC_HANDLER_LIST_SIZE];
int gc_handler_index = -1;

struct semi_space {
	void *bottom, *top, *end;
};

semi_space from_space, to_space;

extern "C" void __init() {
	void* bottom = HeapAlloc(GetProcessHeap(), HEAP_NO_SERIALIZE, GC_HEAP_SIZE);
	void* end = (void*) ((size_t) bottom + GC_HEAP_SIZE);
	void* middle = (void*) ((size_t) bottom + GC_HEAP_SIZE / 2);

	from_space = {bottom, bottom, middle};
	to_space = {middle, middle, end};
}

extern "C" void push_gc_handler(long func) {
	gc_handlers[gc_handler_index] = func;
}

extern "C" void gc_handler_inc() {
	++gc_handler_index;
}

extern "C" void gc_handler_dec() {
	--gc_handler_index;
}

extern "C" bool inFromSpace(void* addr) {
	return from_space.bottom <= addr && addr < from_space.top;
}

void gc(void* fp) {
	//Do forwarding
	int n = gc_handler_index;
	while (n > 0) {
		auto func = (size_t (*)(void*)) gc_handlers[n--];
		func(fp);
		fp = (void*)(*(long*)fp);
	}
	gc_handler_index = -1;

	//Swap spaces
	semi_space tmp = from_space;
	from_space = to_space;
	to_space = tmp;
	//reset to-space
	to_space.top = to_space.bottom;
}

extern "C" void* allocate(size_t n) {
	//OutputDebugStringA("Attempting to allocate memory...");
	//Check if we have space enough to allocate
	if ((size_t) from_space.top + n <= (size_t)from_space.end) {
		void* addr = from_space.top;
		from_space.top = (void*) ((size_t) from_space.top + n);
		//OutputDebugStringA("Memory was allocated!");
		memset(addr, 0, n);
		return addr;
	}
	OutputDebugStringA("Not enough memory. GC'ing...");
	//Not enough space. Do gc'ing.
	//First argument to gc() is the frame pointer of the calling function
	__asm {
		mov eax, [ebp];
		push eax;
		call gc;
		add esp, 4
	}
	OutputDebugStringA("GC completed");
	//Check if we now have space enough
	if ((size_t) from_space.top + n <= (size_t) from_space.end) {
		void* addr = from_space.top;
		from_space.top = (void*) ((size_t) from_space.top + n);
		//OutputDebugStringA("Memory allocated after GC'ing");
		memset(addr, 0, n);
		return addr;
	}
	//OutputDebugStringA("Could not allocate memory after GC'ing");
	return nullptr;
}

extern "C" void* allocInToSpace(size_t n) {
	void* addr = to_space.top;
	to_space.top = (void*) ((size_t) to_space.top + n);
	memset(addr, 0, n);
	return addr;
}

extern "C" void abort(int n) {
	ExitProcess(n);
}

extern "C" void print(int env, void* s) {
	DWORD NumberOfCharsWritten;
	char* str = (char*) ((BYTE*) s + 4);
	WriteConsoleA(GetStdHandle(STD_OUTPUT_HANDLE), str, strlen(str), &NumberOfCharsWritten, NULL);
}