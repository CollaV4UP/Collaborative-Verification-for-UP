// simple example 
type A;
function Decr(x: A) returns (A);
function Incr(x: A) returns (A);
function Next(x: A) returns (A);
procedure main(){
     
   var x, y, z, n1: A;
   
    x := y;

    if(z != n1){
           x := Decr(x);
           x := Incr(x);
           y := Decr(y);
           y := Incr(y);
           z := Next(z);           
        }else{
           x := Incr(x);
           y := Incr(y);         
        }

      assert(x == y);
}
