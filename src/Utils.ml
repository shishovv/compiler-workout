let list_init len f = 
    let rec init acc i = 
        if i == len 
        then List.rev acc
        else init ((f i)::acc) (i + 1) in
    init [] 0
