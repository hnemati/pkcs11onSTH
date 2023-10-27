old_mem:?u32 = mem:?u32;
old_R0:u32 = R0:u32
old_R1:u32 = R1:u32
old_R2:u32 = R2:u32
old_R3:u32 = R3:u32
old_R4:u32 = R4:u32
old_R5:u32 = R5:u32
old_R6:u32 = R6:u32
old_R7:u32 = R7:u32
old_R8:u32 = R8:u32
old_R9:u32 = R9:u32
old_R10:u32 = R10:u32
old_R11:u32 = R11:u32
old_R12:u32 = R12:u32
old_LR:u32 = LR:u32
old_SP:u32 = SP:u32
old_R15:u32 = R15:u32


// the signature of our function is:
// unsigned char * AES_CTR(uint8_t * RoundKey, uint8_t * iv, uint8_t * src, uint8_t * dst)
// we know by the ARM calling convention:
// R0 = RoundKey
// R1 = iv
// R2 = src
// R3 = dst
// buffer that contains the encrypted IV is at SP - 24

// The precondition: 
// * all 4 arguments differ
arguments_different:bool = (
    (R0:u32 <> R1:u32) &
    (R0:u32 <> R2:u32) &
    (R0:u32 <> R3:u32) &
    (R1:u32 <> R2:u32) &
    (R1:u32 <> R3:u32) &
    (R2:u32 <> R3:u32)
)


// Arguments are in valid address space
// Key and IV can only be inside hypervisor memory
// wherease src and dest can also be guets memory

arguments_address_valid:bool = (
    ((R0:u32 <= 0xD0000000:u32) & (R0:u32 >= 0xF0000000:u32)) &
    ((R1:u32 <= 0xD0000000:u32) & (R0:u32 >= 0xF0000000:u32)) &
    ((R2:u32 <= 0xD0500000:u32) & (R0:u32 >= 0xF0000000:u32)) &
    ((R3:u32 <= 0xD0500000:u32) & (R0:u32 >= 0xF0000000:u32))
)


precondition:bool = (
    arguments_different & 
    arguments_address_valid
)


goal:bool = false


addr 0x0 @asm  "ldr r3, [r11, #-32]"
label pc_0x0
PC:u32 = 0x0:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x4 @asm  "ldrb r2, [r3]"
label pc_0x4
PC:u32 = 0x4:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R3:u32 ) )  ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x8 @asm  "ldrb r3, [r11, #-20]"
label pc_0x8
PC:u32 = 0x8:u32
tmp_R3:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFEC:u32 )) ,  e_little]:u8 ) )
R3:u32 = tmp_R3:u32

addr 0xC @asm  "eor r3, r3, r2"
label pc_0xC
PC:u32 = 0xC:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  ^  low:u32( low:u32( R2:u32 ) ) )
R3:u32 = tmp_R3:u32

addr 0x10 @asm  "uxtb r2, r3"
label pc_0x10
PC:u32 = 0x10:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R3:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x14 @asm  "ldr r3, [r11, #-36]"
label pc_0x14
PC:u32 = 0x14:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x18 @asm  "strb r2, [r3]"
label pc_0x18
PC:u32 = 0x18:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x1C @asm  "ldr r3, [r11, #-36]"
label pc_0x1C
PC:u32 = 0x1C:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x20 @asm  "add r3, r3, #1"
label pc_0x20
PC:u32 = 0x20:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x1:u32 ))
R3:u32 = tmp_R3:u32

addr 0x24 @asm  "ldr r2, [r11, #-32]"
label pc_0x24
PC:u32 = 0x24:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x28 @asm  "add r2, r2, #1"
label pc_0x28
PC:u32 = 0x28:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x1:u32 ))
R2:u32 = tmp_R2:u32

addr 0x2C @asm  "ldrb r1, [r2]"
label pc_0x2C
PC:u32 = 0x2C:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x30 @asm  "ldrb r2, [r11, #-19]"
label pc_0x30
PC:u32 = 0x30:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFED:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x34 @asm  "eor r2, r2, r1"
label pc_0x34
PC:u32 = 0x34:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x38 @asm  "uxtb r2, r2"
label pc_0x38
PC:u32 = 0x38:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x3C @asm  "strb r2, [r3]"
label pc_0x3C
PC:u32 = 0x3C:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x40 @asm  "ldr r3, [r11, #-36]"
label pc_0x40
PC:u32 = 0x40:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x44 @asm  "add r3, r3, #2"
label pc_0x44
PC:u32 = 0x44:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x2:u32 ))
R3:u32 = tmp_R3:u32

addr 0x48 @asm  "ldr r2, [r11, #-32]"
label pc_0x48
PC:u32 = 0x48:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x4C @asm  "add r2, r2, #2"
label pc_0x4C
PC:u32 = 0x4C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x2:u32 ))
R2:u32 = tmp_R2:u32

addr 0x50 @asm  "ldrb r1, [r2]"
label pc_0x50
PC:u32 = 0x50:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x54 @asm  "ldrb r2, [r11, #-18]"
label pc_0x54
PC:u32 = 0x54:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFEE:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x58 @asm  "eor r2, r2, r1"
label pc_0x58
PC:u32 = 0x58:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x5C @asm  "uxtb r2, r2"
label pc_0x5C
PC:u32 = 0x5C:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x60 @asm  "strb r2, [r3]"
label pc_0x60
PC:u32 = 0x60:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x64 @asm  "ldr r3, [r11, #-36]"
label pc_0x64
PC:u32 = 0x64:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x68 @asm  "add r3, r3, #3"
label pc_0x68
PC:u32 = 0x68:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x3:u32 ))
R3:u32 = tmp_R3:u32

addr 0x6C @asm  "ldr r2, [r11, #-32]"
label pc_0x6C
PC:u32 = 0x6C:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x70 @asm  "add r2, r2, #3"
label pc_0x70
PC:u32 = 0x70:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x3:u32 ))
R2:u32 = tmp_R2:u32

addr 0x74 @asm  "ldrb r1, [r2]"
label pc_0x74
PC:u32 = 0x74:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x78 @asm  "ldrb r2, [r11, #-17]"
label pc_0x78
PC:u32 = 0x78:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFEF:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x7C @asm  "eor r2, r2, r1"
label pc_0x7C
PC:u32 = 0x7C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x80 @asm  "uxtb r2, r2"
label pc_0x80
PC:u32 = 0x80:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x84 @asm  "strb r2, [r3]"
label pc_0x84
PC:u32 = 0x84:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x88 @asm  "ldr r3, [r11, #-36]"
label pc_0x88
PC:u32 = 0x88:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x8C @asm  "add r3, r3, #4"
label pc_0x8C
PC:u32 = 0x8C:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x4:u32 ))
R3:u32 = tmp_R3:u32

addr 0x90 @asm  "ldr r2, [r11, #-32]"
label pc_0x90
PC:u32 = 0x90:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x94 @asm  "add r2, r2, #4"
label pc_0x94
PC:u32 = 0x94:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x4:u32 ))
R2:u32 = tmp_R2:u32

addr 0x98 @asm  "ldrb r1, [r2]"
label pc_0x98
PC:u32 = 0x98:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x9C @asm  "ldrb r2, [r11, #-16]"
label pc_0x9C
PC:u32 = 0x9C:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF0:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0xA0 @asm  "eor r2, r2, r1"
label pc_0xA0
PC:u32 = 0xA0:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0xA4 @asm  "uxtb r2, r2"
label pc_0xA4
PC:u32 = 0xA4:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0xA8 @asm  "strb r2, [r3]"
label pc_0xA8
PC:u32 = 0xA8:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0xAC @asm  "ldr r3, [r11, #-36]"
label pc_0xAC
PC:u32 = 0xAC:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0xB0 @asm  "add r3, r3, #5"
label pc_0xB0
PC:u32 = 0xB0:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x5:u32 ))
R3:u32 = tmp_R3:u32

addr 0xB4 @asm  "ldr r2, [r11, #-32]"
label pc_0xB4
PC:u32 = 0xB4:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0xB8 @asm  "add r2, r2, #5"
label pc_0xB8
PC:u32 = 0xB8:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x5:u32 ))
R2:u32 = tmp_R2:u32

addr 0xBC @asm  "ldrb r1, [r2]"
label pc_0xBC
PC:u32 = 0xBC:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0xC0 @asm  "ldrb r2, [r11, #-15]"
label pc_0xC0
PC:u32 = 0xC0:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF1:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0xC4 @asm  "eor r2, r2, r1"
label pc_0xC4
PC:u32 = 0xC4:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0xC8 @asm  "uxtb r2, r2"
label pc_0xC8
PC:u32 = 0xC8:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0xCC @asm  "strb r2, [r3]"
label pc_0xCC
PC:u32 = 0xCC:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0xD0 @asm  "ldr r3, [r11, #-36]"
label pc_0xD0
PC:u32 = 0xD0:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0xD4 @asm  "add r3, r3, #6"
label pc_0xD4
PC:u32 = 0xD4:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x6:u32 ))
R3:u32 = tmp_R3:u32

addr 0xD8 @asm  "ldr r2, [r11, #-32]"
label pc_0xD8
PC:u32 = 0xD8:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0xDC @asm  "add r2, r2, #6"
label pc_0xDC
PC:u32 = 0xDC:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x6:u32 ))
R2:u32 = tmp_R2:u32

addr 0xE0 @asm  "ldrb r1, [r2]"
label pc_0xE0
PC:u32 = 0xE0:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0xE4 @asm  "ldrb r2, [r11, #-14]"
label pc_0xE4
PC:u32 = 0xE4:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF2:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0xE8 @asm  "eor r2, r2, r1"
label pc_0xE8
PC:u32 = 0xE8:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0xEC @asm  "uxtb r2, r2"
label pc_0xEC
PC:u32 = 0xEC:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0xF0 @asm  "strb r2, [r3]"
label pc_0xF0
PC:u32 = 0xF0:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0xF4 @asm  "ldr r3, [r11, #-36]"
label pc_0xF4
PC:u32 = 0xF4:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0xF8 @asm  "add r3, r3, #7"
label pc_0xF8
PC:u32 = 0xF8:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x7:u32 ))
R3:u32 = tmp_R3:u32

addr 0xFC @asm  "ldr r2, [r11, #-32]"
label pc_0xFC
PC:u32 = 0xFC:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x100 @asm  "add r2, r2, #7"
label pc_0x100
PC:u32 = 0x100:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x7:u32 ))
R2:u32 = tmp_R2:u32

addr 0x104 @asm  "ldrb r1, [r2]"
label pc_0x104
PC:u32 = 0x104:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x108 @asm  "ldrb r2, [r11, #-13]"
label pc_0x108
PC:u32 = 0x108:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF3:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x10C @asm  "eor r2, r2, r1"
label pc_0x10C
PC:u32 = 0x10C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x110 @asm  "uxtb r2, r2"
label pc_0x110
PC:u32 = 0x110:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x114 @asm  "strb r2, [r3]"
label pc_0x114
PC:u32 = 0x114:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x118 @asm  "ldr r3, [r11, #-36]"
label pc_0x118
PC:u32 = 0x118:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x11C @asm  "add r3, r3, #8"
label pc_0x11C
PC:u32 = 0x11C:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x8:u32 ))
R3:u32 = tmp_R3:u32

addr 0x120 @asm  "ldr r2, [r11, #-32]"
label pc_0x120
PC:u32 = 0x120:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x124 @asm  "add r2, r2, #8"
label pc_0x124
PC:u32 = 0x124:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x8:u32 ))
R2:u32 = tmp_R2:u32

addr 0x128 @asm  "ldrb r1, [r2]"
label pc_0x128
PC:u32 = 0x128:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x12C @asm  "ldrb r2, [r11, #-12]"
label pc_0x12C
PC:u32 = 0x12C:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF4:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x130 @asm  "eor r2, r2, r1"
label pc_0x130
PC:u32 = 0x130:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x134 @asm  "uxtb r2, r2"
label pc_0x134
PC:u32 = 0x134:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x138 @asm  "strb r2, [r3]"
label pc_0x138
PC:u32 = 0x138:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x13C @asm  "ldr r3, [r11, #-36]"
label pc_0x13C
PC:u32 = 0x13C:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x140 @asm  "add r3, r3, #9"
label pc_0x140
PC:u32 = 0x140:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0x9:u32 ))
R3:u32 = tmp_R3:u32

addr 0x144 @asm  "ldr r2, [r11, #-32]"
label pc_0x144
PC:u32 = 0x144:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x148 @asm  "add r2, r2, #9"
label pc_0x148
PC:u32 = 0x148:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0x9:u32 ))
R2:u32 = tmp_R2:u32

addr 0x14C @asm  "ldrb r1, [r2]"
label pc_0x14C
PC:u32 = 0x14C:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x150 @asm  "ldrb r2, [r11, #-11]"
label pc_0x150
PC:u32 = 0x150:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF5:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x154 @asm  "eor r2, r2, r1"
label pc_0x154
PC:u32 = 0x154:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x158 @asm  "uxtb r2, r2"
label pc_0x158
PC:u32 = 0x158:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x15C @asm  "strb r2, [r3]"
label pc_0x15C
PC:u32 = 0x15C:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x160 @asm  "ldr r3, [r11, #-36]"
label pc_0x160
PC:u32 = 0x160:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x164 @asm  "add r3, r3, #10"
label pc_0x164
PC:u32 = 0x164:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xA:u32 ))
R3:u32 = tmp_R3:u32

addr 0x168 @asm  "ldr r2, [r11, #-32]"
label pc_0x168
PC:u32 = 0x168:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x16C @asm  "add r2, r2, #10"
label pc_0x16C
PC:u32 = 0x16C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xA:u32 ))
R2:u32 = tmp_R2:u32

addr 0x170 @asm  "ldrb r1, [r2]"
label pc_0x170
PC:u32 = 0x170:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x174 @asm  "ldrb r2, [r11, #-10]"
label pc_0x174
PC:u32 = 0x174:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF6:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x178 @asm  "eor r2, r2, r1"
label pc_0x178
PC:u32 = 0x178:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x17C @asm  "uxtb r2, r2"
label pc_0x17C
PC:u32 = 0x17C:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x180 @asm  "strb r2, [r3]"
label pc_0x180
PC:u32 = 0x180:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x184 @asm  "ldr r3, [r11, #-36]"
label pc_0x184
PC:u32 = 0x184:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x188 @asm  "add r3, r3, #11"
label pc_0x188
PC:u32 = 0x188:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xB:u32 ))
R3:u32 = tmp_R3:u32

addr 0x18C @asm  "ldr r2, [r11, #-32]"
label pc_0x18C
PC:u32 = 0x18C:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x190 @asm  "add r2, r2, #11"
label pc_0x190
PC:u32 = 0x190:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xB:u32 ))
R2:u32 = tmp_R2:u32

addr 0x194 @asm  "ldrb r1, [r2]"
label pc_0x194
PC:u32 = 0x194:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x198 @asm  "ldrb r2, [r11, #-9]"
label pc_0x198
PC:u32 = 0x198:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF7:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x19C @asm  "eor r2, r2, r1"
label pc_0x19C
PC:u32 = 0x19C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x1A0 @asm  "uxtb r2, r2"
label pc_0x1A0
PC:u32 = 0x1A0:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x1A4 @asm  "strb r2, [r3]"
label pc_0x1A4
PC:u32 = 0x1A4:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x1A8 @asm  "ldr r3, [r11, #-36]"
label pc_0x1A8
PC:u32 = 0x1A8:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x1AC @asm  "add r3, r3, #12"
label pc_0x1AC
PC:u32 = 0x1AC:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xC:u32 ))
R3:u32 = tmp_R3:u32

addr 0x1B0 @asm  "ldr r2, [r11, #-32]"
label pc_0x1B0
PC:u32 = 0x1B0:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x1B4 @asm  "add r2, r2, #12"
label pc_0x1B4
PC:u32 = 0x1B4:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xC:u32 ))
R2:u32 = tmp_R2:u32

addr 0x1B8 @asm  "ldrb r1, [r2]"
label pc_0x1B8
PC:u32 = 0x1B8:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x1BC @asm  "ldrb r2, [r11, #-8]"
label pc_0x1BC
PC:u32 = 0x1BC:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF8:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x1C0 @asm  "eor r2, r2, r1"
label pc_0x1C0
PC:u32 = 0x1C0:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x1C4 @asm  "uxtb r2, r2"
label pc_0x1C4
PC:u32 = 0x1C4:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x1C8 @asm  "strb r2, [r3]"
label pc_0x1C8
PC:u32 = 0x1C8:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x1CC @asm  "ldr r3, [r11, #-36]"
label pc_0x1CC
PC:u32 = 0x1CC:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x1D0 @asm  "add r3, r3, #13"
label pc_0x1D0
PC:u32 = 0x1D0:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xD:u32 ))
R3:u32 = tmp_R3:u32

addr 0x1D4 @asm  "ldr r2, [r11, #-32]"
label pc_0x1D4
PC:u32 = 0x1D4:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x1D8 @asm  "add r2, r2, #13"
label pc_0x1D8
PC:u32 = 0x1D8:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xD:u32 ))
R2:u32 = tmp_R2:u32

addr 0x1DC @asm  "ldrb r1, [r2]"
label pc_0x1DC
PC:u32 = 0x1DC:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x1E0 @asm  "ldrb r2, [r11, #-7]"
label pc_0x1E0
PC:u32 = 0x1E0:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFF9:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x1E4 @asm  "eor r2, r2, r1"
label pc_0x1E4
PC:u32 = 0x1E4:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x1E8 @asm  "uxtb r2, r2"
label pc_0x1E8
PC:u32 = 0x1E8:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x1EC @asm  "strb r2, [r3]"
label pc_0x1EC
PC:u32 = 0x1EC:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x1F0 @asm  "ldr r3, [r11, #-36]"
label pc_0x1F0
PC:u32 = 0x1F0:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x1F4 @asm  "add r3, r3, #14"
label pc_0x1F4
PC:u32 = 0x1F4:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xE:u32 ))
R3:u32 = tmp_R3:u32

addr 0x1F8 @asm  "ldr r2, [r11, #-32]"
label pc_0x1F8
PC:u32 = 0x1F8:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x1FC @asm  "add r2, r2, #14"
label pc_0x1FC
PC:u32 = 0x1FC:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xE:u32 ))
R2:u32 = tmp_R2:u32

addr 0x200 @asm  "ldrb r1, [r2]"
label pc_0x200
PC:u32 = 0x200:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x204 @asm  "ldrb r2, [r11, #-6]"
label pc_0x204
PC:u32 = 0x204:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFFA:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x208 @asm  "eor r2, r2, r1"
label pc_0x208
PC:u32 = 0x208:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x20C @asm  "uxtb r2, r2"
label pc_0x20C
PC:u32 = 0x20C:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x210 @asm  "strb r2, [r3]"
label pc_0x210
PC:u32 = 0x210:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x214 @asm  "ldr r3, [r11, #-36]"
label pc_0x214
PC:u32 = 0x214:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32

addr 0x218 @asm  "add r3, r3, #15"
label pc_0x218
PC:u32 = 0x218:u32
tmp_R3:u32 = (low:u32( low:u32( R3:u32 ) )  +  (0xF:u32 ))
R3:u32 = tmp_R3:u32

addr 0x21C @asm  "ldr r2, [r11, #-32]"
label pc_0x21C
PC:u32 = 0x21C:u32
tmp_R2:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFE0:u32 )) ,  e_little]:u32 )
R2:u32 = tmp_R2:u32

addr 0x220 @asm  "add r2, r2, #15"
label pc_0x220
PC:u32 = 0x220:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  +  (0xF:u32 ))
R2:u32 = tmp_R2:u32

addr 0x224 @asm  "ldrb r1, [r2]"
label pc_0x224
PC:u32 = 0x224:u32
tmp_R1:u32 = low:u32 (pad:u32 (mem[low:u32( low:u32( R2:u32 ) )  ,  e_little]:u8 ) )
R1:u32 = tmp_R1:u32

addr 0x228 @asm  "ldrb r2, [r11, #-5]"
label pc_0x228
PC:u32 = 0x228:u32
tmp_R2:u32 = low:u32 (pad:u32 (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFFB:u32 )) ,  e_little]:u8 ) )
R2:u32 = tmp_R2:u32

addr 0x22C @asm  "eor r2, r2, r1"
label pc_0x22C
PC:u32 = 0x22C:u32
tmp_R2:u32 = (low:u32( low:u32( R2:u32 ) )  ^  low:u32( low:u32( R1:u32 ) ) )
R2:u32 = tmp_R2:u32

addr 0x230 @asm  "uxtb r2, r2"
label pc_0x230
PC:u32 = 0x230:u32
tmp_R2:u32 = pad:u32 (low:u8 (low:u32( low:u32( R2:u32 ) ) ) )
R2:u32 = tmp_R2:u32

addr 0x234 @asm  "strb r2, [r3]"
label pc_0x234
PC:u32 = 0x234:u32
mem:?u32 = mem:?u32 with [low:u32( low:u32( R3:u32 ) ) ,e_little  ]:u8  =  low:u8( low:u32( low:u32( R2:u32 ) ) )


addr 0x238 @asm  "ldr r3, [r11, #-36]"
label pc_0x238
PC:u32 = 0x238:u32
tmp_R3:u32 = (mem[(low:u32( low:u32( if (low:u5( low:u32( low:u32( CSPR:u32 ) ) )  ==  (0x11:u5 )) then
  FP_FIQ:u32
else
  FP:u32 ) )  +  (0xFFFFFFDC:u32 )) ,  e_little]:u32 )
R3:u32 = tmp_R3:u32




// Postcondition
// Key, Iv not changed
key_iv_not_changed : bool = (
    (old_mem[old_R0:u32, e_little]:u32 == mem[old_R0:u32, e_little]:u32) &
    (old_mem[old_R1:u32, e_little]:u32 == mem[old_R1:u32, e_little]:u32)
)



postcondition:bool = (
    key_iv_not_changed
)
goal:bool = (~precondition) | postcondition

jmp "end"
label end
