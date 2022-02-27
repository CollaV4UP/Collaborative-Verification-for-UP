type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, s, t, u1, u5, v4, v6, x, y, z: A;

	x := y;

	if (s == v4) {
		x := f(x);
		x := h(x);
		y := f(y);
		y := h(y);
	} else {
			if (s == u1) {
				x := f(t);
				y := f(k);
				assume(t == k);
				x := h(x);
				y := h(y);
			}
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
		x := f(x);
	}

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
		x := f(x);
		y := f(y);
	}

	assert(x == y);
}