type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
function l(x: A) returns (A);
procedure main(){

	var k, r0, s, t, u1, u3, u7, w1, w2, w3, w4, x, y: A;

	x := y;

	if (s == u7) {
		while (w1 != w2) {
			if (w3 == w4) {
				x := f(x);
				y := f(y);
				w3 := l(w3);
				assume(w3 != w4);
			} else {
				x := h(x);
				y := h(y);
				w4 := l(w4);
				assume(w3 == w4);
			}
			w1 := f(w1);
		}
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

	if (s == r0) {
		x := f(x);
		y := f(y);
	} else {
		x := f(x);
		y := f(y);
	}

	assert(x == y);
}