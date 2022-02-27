type A;
function f(x: A) returns (A);
procedure main(){

	var k, s, t, u5, v6, x, y, z: A;

	x := y;

	if (s == v6) {
		x := t;
		y := k;
		assume(t == k);
		while (y != z){
			x := f(x);
			y := f(y);
			z := f(z);
		}
	} else {
			if (s == u5) {
				x := t;
				y := k;
				while (y != z){
					x := f(x);
					y := f(y);
					z := f(z);
				}
				assume(t == k);
			}
	}

	assert(x == y);
}