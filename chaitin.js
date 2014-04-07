
(function (global) {
    // S-expressions
    function Sexp () {
        this.hd = null;
        this.tl = null;
        this.at = false;
        this.nmb = false;
        this.err = false;
        this.pname = null;
        this.nval = null;
        this.vstk = null;
        this.str = null;
    }
    Sexp.createFromSexp = function (h, t) {
        var sexp = new Sexp();
        sexp.hd = h;
        sexp.tl = t;
        sexp.pname = "";
        sexp.nval = 0;
        return sexp;
    };
    Sexp.createFromString = function (s) {
        var sexp = new Sexp();
        sexp.at = true;
        sexp.pname = s;
        sexp.nval = 0;
        sexp.hd = sexp;
        sexp.tl = sexp;
        sexp.vstk = [sexp];
        return sexp;
    };
    Sexp.createFromNumber = function (n) {
        var sexp = new Sexp();
        sexp.at = true;
        sexp.nmb = true;
        sexp.nval = n;
        sexp.pname = n.toString();
        sexp.hd = sexp;
        sexp.tl = sexp;
        sexp.vstk = [sexp];
        return sexp;
    };

    Sexp.prototype = {
        two:    function () {
            return this.tl.hd;
        }
    ,   three:  function () {
            return this.tl.tl.hd;
        }
    ,   four:   function () {
            return this.tl.tl.tl.hd;
        }
    ,   bad:    function () {
            if (this.at) return this.pname === ")";
            return this.hd.bad() || this.tl.bad();
        }
    ,   toString:   function () {
            var stringify = function (x) {
                if (x.at && x.pname !== "") {
                    this.str += x.pname;
                    return;
                }
                this.str += "(";
                while (!x.at) {
                    stringify(x.hd);
                    x = x.tl;
                    if (!x.at) this.str += " ";
                }
                this.str += ")";
            };
            this.str = "";
            stringify(this);
            var ret = this.str;
            this.str = null;
            return ret;
        }
    };


    
}(window || exports));
