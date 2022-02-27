type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, r0, s, t, u3, u5, v6, x, y, z: A;

	x := y;

	if (s == u5) {
		x := t;
		y := k;
		while (y != z){
			x := f(x);
			y := f(y);
			z := f(z);
		}
		assume(t == k);
	} else {
		x := f(x);
	}

	if (s == r0) {
		x := f(x);
		y := f(y);
	} else {
		x := f(x);
		y := f(y);
	}

	if (s == u3) {
		x := f(x);
		y := f(y);
		x := h(x);
		y := h(y);
	} else {
			if (s == v6) {
				x := t;
				y := k;
				assume(t == k);
				while (y != z){
					x := f(x);
					y := f(y);
					z := f(z);
				}
			}
	}

	assert(x == y);
}