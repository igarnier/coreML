type fresh_seed = int
type t = int Utils.FreshGen.acc

let initial = Utils.FreshGen.initial 0 succ

let next = Utils.FreshGen.fresh
    
let var x = "v"^(string_of_int x)

let nextvar freshgen = 
  let (fg, x) = Utils.FreshGen.fresh freshgen in
    (fg, var x)

let varcap x = "V"^(string_of_int x)
