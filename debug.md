```
Left = S -> U & T -> U
S := {flag, flag}
T := {flag, {flag, flag}}
U := {{flag, flag}, {flag, flag}}
:= 
        (
          ({flag, flag}         -> {{flag, flag}, {flag, flag}}) 
        & ({flag, {flag, flag}} -> {{flag, flag}, {flag, flag}})
        )

:= S -> U & T -> U



Right := 
       ({flag, flag} | {flag, {flag, flag}} -> {{flag, flag}, {flag,flag}})

!Right: := 
       (flag |
        {Any, Any} |
        (!({flag,flag} | {flag,{flag, flag}} -> {{flag, flag}, {flag, flag}})))

:= !flag U !Product U !(S | T -> U)

Left & !Right :=

S -> U & T -> U & !(S | T -> U)
```