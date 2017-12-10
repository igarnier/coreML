include ExtMap.Make(struct
  type t = string
      
  let compare (x : string) (y : string) = 
    if x = y 
    then 0
    else if x < y
    then (-1)
    else 1

end)
