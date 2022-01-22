// related to mark and sweep
datatype Color = White | Gray | Black | Bad

function interpret(bucket: bv32, index: int) : seq<Color> 
    requires 0<=index<=15
    decreases(16-index);  
{
    var mask:bv32 := 3;
    var bucket := bucket >> (index*2);
    var color_bit: bv32 := bucket & mask;
    var c : Color := 
    if color_bit == 0 then
        White
    else if color_bit == 1 then
        Gray
    else if color_bit == 2 then
        Black
    else
        Bad;

    if index== 15 then 
        [c]
    else 
        interpret(bucket, index+1) + [c]
}

method set_color(bucket: bv32, c:Color, index: int, ghost g_bucket: seq<Color>) returns (new_bucket:bv32) 
  requires 0<= index < 16;
  requires interpret(bucket, 0) == g_bucket;
  ensures interpret(new_bucket, 0) == g_bucket[index := c];
{
    var mask:bv32 := 3;
    mask := mask << (index*2);
    mask := !mask;
    new_bucket := bucket & mask;

    var num_color:bv32 := 
        if c == White then
            0
        else if c == Gray then
            1
        else if c == Black then
            2
        else
            3;
    
    num_color := num_color << (index*2);
    new_bucket := new_bucket | num_color;
}
    
