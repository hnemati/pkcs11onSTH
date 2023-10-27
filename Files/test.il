precondition:bool = (
    (a:u32 <> b:u32)
)

a:u32 = a:u32 + 0x1:u32


postcondition:bool = (
    (a:u32 == b:u32)
)

goal:bool = (~precondition) | postcondition

