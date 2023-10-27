old_mem:?u32 = mem:?u32;

inv_mem:bool = (
    (old_mem[0x224:u32 , e_little]:u32 == 0x123:u32)
)


precondition:bool = inv_mem:bool

postcondition:bool = true

goal:bool = (~precondition | postcondition)



