type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, r0, s, t, u1, u5, v4, x, y, z: A;

	x := y;

	if (s == u1) {
		x := f(t);
		y := f(k);
		assume(t == k);
		x := h(x);
		y := h(y);
	} else {
		x := f(x);
		y := f(y);
	}

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
			if (s == r0) {
				x := f(x);
				y := f(y);
			}
	}

	if (s == v4) {
		x := f(x);
		x := h(x);
		y := f(y);
		y := h(y);
	} else {
		x := f(x);
		y := f(y);
	}

	assert(x == y);
}