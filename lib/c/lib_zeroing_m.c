#ifndef _Lib_Zero_H
#define _Lib_Zero_H

void clear_u64(void* b, unsigned int len)
{
	volatile uint64_t *v = mem;
	for (unsigned int i = 0; i < len; i++)
	{
		v[i] = (uint64_t)0;
	}
}

void Lib_Memzero2_mem_zero_u64(void* b, unsigned int len)
{

	#if defined(_WIN32) || defined(_WIN64)
    	#include <windows.h>
    	#include <winnt.h>

		RtlSecureZeroMemory(b, sizeof(uint64_t) * l);

	#elif defined(__STDC_LIB_EXT1__)
  		memset_s(b, l, 0, l);

  	#elif defined(BSD)
  		explicit_bzero(b, len);


  	#else
  		clear_u64(b, len);
	#endif 


}

#endif

// https://gcc.gnu.org/wiki/C11Status
// x86_64-w64-mingw32-g++ -mwindows -o ..//test.exe './test.c' 


// https://man.openbsd.org/explicit_bzero.3