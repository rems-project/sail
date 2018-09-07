////////////////////////////////////////////////////////////////
// ELF Loader
////////////////////////////////////////////////////////////////

// Header files for simulator
#include "elf.h"
#include "rts.h"
#include "sail.h"

// Use the zlib library to uncompress ELF.gz files
#include <zlib.h>

// Define ELF constants/types. These come from the
// Tool Interface Standard Executable and Linking Format Specification 1.2

typedef uint32_t Elf32_Addr;
typedef uint16_t Elf32_Half;
typedef uint32_t Elf32_Off;
typedef uint32_t Elf32_Word;

typedef uint64_t Elf64_Addr;
typedef uint16_t Elf64_Half;
typedef uint64_t Elf64_Off;
typedef uint32_t Elf64_Word;
typedef uint64_t Elf64_Xword;

/* Type for section indices, which are 16-bit quantities.  */
typedef uint16_t Elf32_Section;
typedef uint16_t Elf64_Section;

/* Type for version symbol information.  */
typedef Elf32_Half Elf32_Versym;
typedef Elf64_Half Elf64_Versym;

// Big-Endian support functions which reverse values

uint16_t rev16(uint16_t x) {
    uint16_t a = (x >> 0) & 0xff;
    uint16_t b = (x >> 8) & 0xff;
    return (a << 8) | (b << 0);
}

uint32_t rev32(uint32_t x) {
    uint32_t a = (x >> 0) & 0xff;
    uint32_t b = (x >> 8) & 0xff;
    uint32_t c = (x >> 16) & 0xff;
    uint32_t d = (x >> 24) & 0xff;
    return (a << 24) | (b << 16) | (c << 8) | (d << 0);
}

uint64_t rev64(uint64_t x) {
    uint64_t a = (x >> 0) & 0xff;
    uint64_t b = (x >> 8) & 0xff;
    uint64_t c = (x >> 16) & 0xff;
    uint64_t d = (x >> 24) & 0xff;
    uint64_t e = (x >> 32) & 0xff;
    uint64_t f = (x >> 40) & 0xff;
    uint64_t g = (x >> 48) & 0xff;
    uint64_t h = (x >> 56) & 0xff;
    return (a << 56) | (b << 48) | (c << 40) | (d << 32) | (e << 24) | (f << 16) | (g << 8) | (h << 0);
}

// Endian support macros which reverse values on big-endian machines
// (We assume that the host machine is little-endian)

#define rdAddr32(le, x)  ((le) ? (x) : rev32(x))
#define rdHalf32(le, x)  ((le) ? (x) : rev16(x))
#define rdOff32(le, x)   ((le) ? (x) : rev32(x))
#define rdWord32(le, x)  ((le) ? (x) : rev32(x))

#define rdAddr64(le, x)  ((le) ? (x) : rev64(x))
#define rdHalf64(le, x)  ((le) ? (x) : rev16(x))
#define rdOff64(le, x)   ((le) ? (x) : rev64(x))
#define rdWord64(le, x)  ((le) ? (x) : rev32(x))
#define rdXword64(le, x) ((le) ? (x) : rev64(x))


#define EI_NIDENT      16  /* Size of e_ident */

#define EI_MAG0         0  /* Offsets in e_ident */
#define EI_MAG1         1
#define EI_MAG2         2
#define EI_MAG3         3
#define EI_CLASS        4
#define EI_DATA         5

#define ELFMAG0      0x7f  /* Magic string */
#define ELFMAG1       'E'
#define ELFMAG2       'L'
#define ELFMAG3       'F'

#define ELFCLASS32      1  /* 32-bit ELF */
#define ELFCLASS64      2  /* 64-bit ELF */

#define ELFDATA2LSB     1  /* Little-endian ELF */

#define ET_EXEC         2  /* Executable file */

#define EM_ARM     0x0028  /* 32-bit ARM */
#define EM_AARCH64 0x00B7  /* 64-bit ARM */
#define EM_RISCV   0x00F3  /* RISC-V */

#define PT_LOAD         1  /* Loadable segment */

#define SHT_SYMTAB      2  /* Symbol table type */

/* How to extract and insert information held in the st_info field.  */

#define ELF32_ST_BIND(val)        (((unsigned char) (val)) >> 4)
#define ELF32_ST_TYPE(val)        ((val) & 0xf)
#define ELF32_ST_INFO(bind, type) (((bind) << 4) + ((type) & 0xf))

/* Both Elf32_Sym and Elf64_Sym use the same one-byte st_info field.  */
#define ELF64_ST_BIND(val)        ELF32_ST_BIND (val)
#define ELF64_ST_TYPE(val)        ELF32_ST_TYPE (val)
#define ELF64_ST_INFO(bind, type) ELF32_ST_INFO ((bind), (type))


/* Legal values for ST_TYPE subfield of st_info (symbol type).  */

#define STT_NOTYPE     0        /* Symbol type is unspecified */
#define STT_OBJECT     1        /* Symbol is a data object */
#define STT_FUNC       2        /* Symbol is a code object */
#define STT_SECTION    3        /* Symbol associated with a section */
#define STT_FILE       4        /* Symbol's name is file name */
#define STT_COMMON     5        /* Symbol is a common data object */
#define STT_TLS        6        /* Symbol is thread-local data object*/
#define STT_NUM        7        /* Number of defined types.  */
#define STT_LOOS      10        /* Start of OS-specific */
#define STT_GNU_IFUNC 10        /* Symbol is indirect code object */
#define STT_HIOS      12        /* End of OS-specific */
#define STT_LOPROC    13        /* Start of processor-specific */
#define STT_HIPROC    15        /* End of processor-specific */


typedef struct
{
    uint8_t     e_ident[EI_NIDENT]; /* ELF file identifier */
    Elf32_Half  e_type;             /* Object file type */
    Elf32_Half  e_machine;          /* Processor architecture */
    Elf32_Word  e_version;          /* Object file version */
    Elf32_Addr  e_entry;            /* Entry point (loader jumps to this virtual address if != 0) */
    Elf32_Off   e_phoff;            /* Program header table offset */
    Elf32_Off   e_shoff;            /* Section header table offset */
    Elf32_Word  e_flags;            /* Processor-specific flags */
    Elf32_Half  e_ehsize;           /* ELF header size */
    Elf32_Half  e_phentsize;        /* Size of a single program header */
    Elf32_Half  e_phnum;            /* Number of program headers in table */
    Elf32_Half  e_shensize;         /* Size of a single section header */
    Elf32_Half  e_shnum;            /* Number of section headers in table */
    Elf32_Half  e_shtrndx;          /* Index of string table in section header table */
} Elf32_Ehdr;

typedef struct
{
    Elf32_Word  p_type;             /* Segment type */
    Elf32_Off   p_offset;           /* Segment offset in file */
    Elf32_Addr  p_vaddr;            /* Segment load virtual address */
    Elf32_Addr  p_paddr;            /* Segment load physical address */
    Elf32_Word  p_filesz;           /* Segment size in file */
    Elf32_Word  p_memsz;            /* Segment size in memory. Must be >= p_filesz. If > p_filesz, zero pad */
    Elf32_Word  p_flags;            /* Segment flags */
    Elf32_Word  p_align;            /* Segment alignment */
} Elf32_Phdr;

typedef struct
{
    uint8_t     e_ident[EI_NIDENT]; /* ELF file identifier */
    Elf64_Half  e_type;             /* Object file type */
    Elf64_Half  e_machine;          /* Processor architecture */
    Elf64_Word  e_version;          /* Object file version */
    Elf64_Addr  e_entry;            /* Entry point (loader jumps to this virtual address if != 0) */
    Elf64_Off   e_phoff;            /* Program header table offset */
    Elf64_Off   e_shoff;            /* Section header table offset */
    Elf64_Word  e_flags;            /* Processor-specific flags */
    Elf64_Half  e_ehsize;           /* ELF header size */
    Elf64_Half  e_phentsize;        /* Size of a single program header */
    Elf64_Half  e_phnum;            /* Number of program headers in table */
    Elf64_Half  e_shensize;         /* Size of a single section header */
    Elf64_Half  e_shnum;            /* Number of section headers in table */
    Elf64_Half  e_shtrndx;          /* Index of string table in section header table */
} Elf64_Ehdr;

typedef struct
{
    Elf64_Word  p_type;             /* Segment type */
    Elf64_Word  p_flags;            /* Segment flags */
    Elf64_Off   p_offset;           /* Segment offset in file */
    Elf64_Addr  p_vaddr;            /* Segment load virtual address */
    Elf64_Addr  p_paddr;            /* Segment load physical address */
    Elf64_Xword p_filesz;           /* Segment size in file */
    Elf64_Xword p_memsz;            /* Segment size in memory. Must be >= p_filesz.
                                       If > p_filesz, zero pad memory */
    Elf64_Xword p_align;            /* Segment alignment */
} Elf64_Phdr;

typedef struct
{
    Elf32_Word  sh_name;            /* Section name (string tbl index) */
    Elf32_Word  sh_type;            /* Section type */
    Elf32_Word  sh_flags;           /* Section flags */
    Elf32_Addr  sh_addr;            /* Section virtual addr at execution */
    Elf32_Off   sh_offset;          /* Section file offset */
    Elf32_Word  sh_size;            /* Section size in bytes */
    Elf32_Word  sh_link;            /* Link to another section */
    Elf32_Word  sh_info;            /* Additional section information */
    Elf32_Word  sh_addralign;       /* Section alignment */
    Elf32_Word  sh_entsize;         /* Entry size if section holds table */
} Elf32_Shdr;

typedef struct
{
    Elf64_Word  sh_name;            /* Section name (string tbl index) */
    Elf64_Word  sh_type;            /* Section type */
    Elf64_Xword sh_flags;           /* Section flags */
    Elf64_Addr  sh_addr;            /* Section virtual addr at execution */
    Elf64_Off   sh_offset;          /* Section file offset */
    Elf64_Xword sh_size;            /* Section size in bytes */
    Elf64_Word  sh_link;            /* Link to another section */
    Elf64_Word  sh_info;            /* Additional section information */
    Elf64_Xword sh_addralign;       /* Section alignment */
    Elf64_Xword sh_entsize;         /* Entry size if section holds table */
} Elf64_Shdr;

/* Symbol table entry.  */

typedef struct
{
    Elf32_Word    st_name;          /* Symbol name (string tbl index) */
    Elf32_Addr    st_value;         /* Symbol value */
    Elf32_Word    st_size;          /* Symbol size */
    uint8_t       st_info;          /* Symbol type and binding */
    uint8_t       st_other;         /* Symbol visibility */
    Elf32_Section st_shndx;         /* Section index */
} Elf32_Sym;

typedef struct
{
    Elf64_Word    st_name;          /* Symbol name (string tbl index) */
    uint8_t       st_info;          /* Symbol type and binding */
    uint8_t       st_other;         /* Symbol visibility */
    Elf64_Section st_shndx;         /* Section index */
    Elf64_Addr    st_value;         /* Symbol value */
    Elf64_Xword   st_size;          /* Symbol size */
} Elf64_Sym;

void loadBlock32(const char* buffer, Elf32_Off off, Elf32_Addr addr, Elf32_Word filesz, Elf32_Word memsz) {
    //// std::cout << "Loading block from " << off << " to " << addr << "+:" << filesz << std::endl;
    for(Elf32_Off i = 0; i < filesz; ++i) {
        //// std::cout << "Writing " << (int)buffer[off+i] << " to " << addr+i << std::endl;
	write_mem(addr+i, 0xff & buffer[off+i]);
    }
    // Zero fill if p_memsz > p_filesz
    for(Elf32_Off i = filesz; i < memsz; ++i) {
	write_mem(addr+i, 0);
    }
}

void loadProgHdr32(bool le, const char* buffer, Elf32_Off off, const int total_file_size) {
    //// std::cout << "Loading program header at " << off << std::endl;
    if (off > total_file_size - sizeof(Elf32_Phdr)) {
      fprintf(stderr, "Invalid ELF file, section header overruns end of file\n");
      exit(EXIT_FAILURE);
    }
    Elf32_Phdr *phdr = (Elf32_Phdr*) &buffer[off];
    // Only PT_LOAD segments should be loaded;
    if (rdWord32(le, phdr->p_type) == PT_LOAD) {
        Elf32_Off off = rdOff32(le, phdr->p_offset);
        Elf32_Word filesz = rdWord32(le, phdr->p_filesz);
        if (filesz > total_file_size - off) {
	    fprintf(stderr, "Invalid ELF file, section overruns end of file\n");
	    exit(EXIT_FAILURE);
        }
        loadBlock32(buffer, off, rdAddr32(le, phdr->p_paddr), filesz, rdWord32(le, phdr->p_memsz));
    }
}

void loadBlock64(const char* buffer, Elf64_Off off, Elf64_Addr addr, Elf64_Word filesz, Elf64_Word memsz) {
    //// std::cout << "Loading block from " << off << " to " << addr << "+:" << filesz << std::endl;
    for(Elf64_Off i = 0; i < filesz; ++i) {
        // fprintf(stderr, "Writing 0x%x to 0x%lx\n", (int)buffer[off+i], addr+i);
	write_mem(addr+i, 0xff & buffer[off+i]);
    }
    // Zero fill if p_memsz > p_filesz
    for(Elf64_Off i = filesz; i < memsz; ++i) {
	write_mem(addr+i, 0);
    }
}

void loadProgHdr64(bool le, const char* buffer, Elf64_Off off, const int total_file_size) {
    //// std::cout << "Loading program header at " << off << std::endl;
    if (off > total_file_size - sizeof(Elf64_Phdr)) {
      fprintf(stderr, "Invalid ELF file, section header overruns end of file\n");
      exit(EXIT_FAILURE);
    }
    Elf64_Phdr *phdr = (Elf64_Phdr*) &buffer[off];
    // Only PT_LOAD segments should be loaded;
    if (rdWord64(le, phdr->p_type) == PT_LOAD) {
        Elf64_Off off = rdOff64(le, phdr->p_offset);
        Elf64_Word filesz = rdXword64(le, phdr->p_filesz);
        if (filesz > total_file_size - off) {
	  fprintf(stderr, "Invalid ELF file, section overruns end of file\n");
	  exit(EXIT_FAILURE);
        }
        loadBlock64(buffer, off, rdAddr64(le, phdr->p_paddr), filesz, rdXword64(le, phdr->p_memsz));
    }
}

void loadELFHdr(const char* buffer, const int total_file_size) {
    if (total_file_size < sizeof(Elf32_Ehdr)) {
        fprintf(stderr, "File too small, not big enough even for 32-bit ELF header\n");
        exit(EXIT_FAILURE);
    }
    Elf32_Ehdr *hdr = (Elf32_Ehdr*) &buffer[0]; // both Elf32 and Elf64 have same magic
    if (hdr->e_ident[EI_MAG0] != ELFMAG0 ||
        hdr->e_ident[EI_MAG1] != ELFMAG1 ||
        hdr->e_ident[EI_MAG2] != ELFMAG2 ||
        hdr->e_ident[EI_MAG3] != ELFMAG3) {
        fprintf(stderr, "Invalid ELF magic bytes. Not an ELF file?\n");
        exit(EXIT_FAILURE);
    }

    if (hdr->e_ident[EI_CLASS] == ELFCLASS32) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf32_Ehdr *ehdr = (Elf32_Ehdr*) &buffer[0];
        if (rdHalf32(le, ehdr->e_type) != ET_EXEC ||
            (rdHalf32(le, ehdr->e_machine) != EM_ARM &&
             rdHalf64(le, ehdr->e_machine) != EM_RISCV)) {
            fprintf(stderr, "Invalid ELF type or machine for class (32-bit)\n");
            exit(EXIT_FAILURE);
        }

	for(int i = 0; i < rdHalf32(le, ehdr->e_phnum); ++i) {
	  loadProgHdr32(le, buffer, rdOff32(le, ehdr->e_phoff) + i * rdHalf32(le, ehdr->e_phentsize), total_file_size);
	}

	return;
    } else if (hdr->e_ident[EI_CLASS] == ELFCLASS64) {
        if (total_file_size < sizeof(Elf64_Ehdr)) {
            fprintf(stderr, "File too small, specifies 64-bit ELF but not big enough for 64-bit ELF header\n");
            exit(EXIT_FAILURE);
        }
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf64_Ehdr *ehdr = (Elf64_Ehdr*) &buffer[0];
        if (rdHalf64(le, ehdr->e_type) != ET_EXEC ||
            (rdHalf64(le, ehdr->e_machine) != EM_AARCH64 &&
             rdHalf64(le, ehdr->e_machine) != EM_RISCV)) {
            fprintf(stderr, "Invalid ELF type or machine for class (64-bit)\n");
            exit(EXIT_FAILURE);
        }

	for(int i = 0; i < rdHalf64(le, ehdr->e_phnum); ++i) {
	  loadProgHdr64(le, buffer, rdOff64(le, ehdr->e_phoff) + i * rdHalf64(le, ehdr->e_phentsize), total_file_size);
	}

	return;
    } else {
        fprintf(stderr, "Unrecognized ELF file format\n");
        exit(EXIT_FAILURE);
    }
}

void load_elf(char *filename) {
    // Read input file into memory
    char* buffer = NULL;
    int   size   = 0;
    int   chunk  = (1<<24); // increments output buffer this much
    int   read   = 0;
    gzFile in = gzopen(filename, "rb");
    if (in == NULL) { goto fail; }
    while (!gzeof(in)) {
        size = read + chunk;
        buffer = (char*)realloc(buffer, size);
        if (buffer == NULL) { goto fail; }

        int s = gzread(in, buffer+read, size - read);
        if (s < 0) { goto fail; }
        read += s;
    }

    loadELFHdr(buffer, read);
    free(buffer);
    return;

fail:
    fprintf(stderr, "Unable to read file %s\n", filename);
    exit(EXIT_FAILURE);
}

////////////////////////////////////////////////////////////////
// ELF Loader
////////////////////////////////////////////////////////////////

