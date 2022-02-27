type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, r0, s, t, u1, u3, v2, v4, x, y: A;

	x := y;

	if (s == v2) {
		x := f(t);
		y := f(k);
		x := h(x);
		y := h(y);
		assume(t == k);
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
			if (s == u1) {
				x := f(t);
				y := f(k);
				assume(t == k);
				x := h(x);
				y := h(y);
			}
	}

	if (s == v4) {
		x := f(x);
		x := h(x);
		y := f(y);
		y := h(y);
	} else {
			if (s == r0) {
				x := f(x);
				y := f(y);
			}
	}

	assert(x == y);
}