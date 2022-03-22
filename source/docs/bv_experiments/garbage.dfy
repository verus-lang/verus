// related to mark and sweep
// datatype Color = White | Gray | Black | Bad

// function interpret(bucket: bv32, index: int) : seq<Color> 
//     requires 0<=index<=15
//     decreases(16-index);  
// {
//     var mask:bv32 := 3;
//     var bucket := bucket >> (index*2);
//     var color_bit: bv32 := bucket & mask;
//     var c : Color := 
//     if color_bit == 0 then
//         White
//     else if color_bit == 1 then
//         Gray
//     else if color_bit == 2 then
//         Black
//     else
//         Bad;

//     if index== 15 then 
//         [c]
//     else 
//         interpret(bucket, index+1) + [c]
// }

// method set_color(bucket: bv32, c:Color, index: int, ghost g_bucket: seq<Color>) returns (new_bucket:bv32) 
//   requires 0<= index < 16;
//   requires interpret(bucket, 0) == g_bucket;
//   ensures interpret(new_bucket, 0) == g_bucket[index := c];
// {
//     var mask:bv32 := 3;
//     mask := mask << (index*2);
//     mask := !mask;
//     new_bucket := bucket & mask;

//     var num_color:bv32 := 
//         if c == White then
//             0
//         else if c == Gray then
//             1
//         else if c == Black then
//             2
//         else
//             3;
    
//     num_color := num_color << (index*2);
//     new_bucket := new_bucket | num_color;
// }

type uint5  = i :int | 0 <= i < 32
type uint32 = i :int | 0 <= i < 4294967296

function method get_bit(bv: uint32, i: uint5): bool

function method set_bit(bv: uint32, i: uint5, b: bool): (bv': uint32)
    ensures forall j: uint5 :: (j != i) ==> (get_bit(bv', j) == get_bit(bv, i))
    ensures get_bit(bv', i) == b

function bv_view_aux(bv: uint32, i: uint5): seq<bool>
{
    if i == 0 then
        [get_bit(bv, 0)]
    else
       bv_view_aux(bv, i - 1) + [get_bit(bv, i)]
}

lemma bv_view_aux_correspond(bv: uint32, i: uint5)
    ensures |bv_view_aux(bv, i)| == i + 1
    ensures forall j: uint5 :: (j < i) ==> bv_view_aux(bv, i)[j] == get_bit(bv, j)
{
    if i != 0 {
        bv_view_aux_correspond(bv, i - 1);
        var preI := bv_view_aux(bv, i - 1);
        var curI := bv_view_aux(bv, i);

        assert forall j: uint5 :: (j < i - 1) ==> preI[j] == get_bit(bv, j);
        assert preI + [get_bit(bv, i)] == curI;

        forall j: uint5
            ensures j < i ==> curI[j] == get_bit(bv, j);
        {
            if j < i - 1 {
                assert curI[j] == preI[j];
            } else if j < i {
                assert j == i - 1;
                assert curI[j] == get_bit(bv, j);
            }
        }
    }
}

function bv_view(bv: uint32): seq<bool>
{
    bv_view_aux(bv, 31)
}

lemma bv_view_correspond(bv: uint32)
    ensures |bv_view(bv)| == 32
    ensures forall i: uint5 :: bv_view(bv)[i] == get_bit(bv, i)
{
    bv_view_aux_correspond(bv, 31);
}
