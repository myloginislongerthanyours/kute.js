/* KUTE.js - The Light Tweening Engine
 * package - SVG Plugin
 * desc - draw SVG strokes, morph SVG and SVG transforms
 * by dnp_theme
 * Licensed under MIT-License
 */

(function (root,factory) {
  if (typeof define === 'function' && define.amd) {
    define(['./kute.js'], factory);
  } else if(typeof module == 'object' && typeof require == 'function') {
    module.exports = factory(require('./kute.js'));
  } else if ( typeof root.KUTE !== 'undefined' ) {
    factory(root.KUTE);
  } else {
    throw new Error("SVG Plugin require KUTE.js.");
  }
}(this, function(KUTE) {
  'use strict';

  var g = typeof global !== 'undefined' ? global : window, K = KUTE, // connect plugin to KUTE object and global
    DOM = K.dom, parseProperty = K.parseProperty, prepareStart = K.prepareStart, getCurrentStyle = K.getCurrentStyle,
    trueColor = K.truC, trueDimension = K.truD, crossCheck = K.crossCheck,
    number = g.Interpolate.number, unit = g.Interpolate.unit, color = g.Interpolate.color, // interpolate functions
    defaultOptions = K.defaultOptions, // default tween options since 1.6.1

    // browser detection
    isIE = new RegExp("MSIE ([0-9]{1,}[\.0-9]{0,})").exec(navigator.userAgent) !== null ? parseFloat( RegExp.$1 ) : false,
    isMobile = /iPhone|iPad|iPod|Android/i.test(navigator.userAgent); // we optimize morph depending on device type

  if (isIE&&isIE<9) {return;} // return if SVG API is not supported

  // here we go with the plugin
  var pathRegs = {
      minimalQualifier : /^\s*m/i,
      fullQualifier    : /^\s*m(?:(?:\s*[mlhv]\s*)|(?:\s*(?:[-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?)\s*(?:,(?=\s*[-+.\d]))?))+z\s*$/i,
      polyPointsTokenizer : /(?:[\s,]*((?:[-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?(?:(?:\s+,?\s*)|(?:,\s*)|$)){2}))/g,
      stickyTokenizer     : /(?:\s*([mlhvz])\s*)|(?:\s*([-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?)\s*(?:,(?=\s*[-+.\d]))?)/iy,
      pedanticTokenizer   : /(?:\s*([mlhvz])\s*)|(?:\s*([-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?)\s*(?:,(?=\s*[-+.\d]))?)|((?:[^-+\d.emlhvz]|[-+](?!\.?\d)|\.(?!\d)|e)+)/gi,
  },
  defaultQualifier = pathRegs.minimalQualifier,
  defaultTokenizer = isIE ? pathRegs.pedanticTokenizer : pathRegs.stickyTokenizer,
  ns = 'http://www.w3.org/2000/svg',
  trunc = [ // truncate to 0-2 decimal places
    function(v) { return v >> 0; },
    function(v) { return ((v * 10) >> 0) / 10; },
    function(v) { return ((v * 100) >> 0) / 100; }, ],
  round = [ // round to 0-2 decimal places
    function(v) { return Math.round(v); },
    function(v) { return Math.round(v * 10) / 10; },
    function(v) { return Math.round(v * 100) / 100; }, ],
  coordPrecision = isMobile ? trunc[0] : round[1], // use truncation on mobile, subpixel rounding on desktop
  coords = g.Interpolate.coords = function(a, b, l, v) { // sa, sa, al, [0..1] -> ps | interpolation function for path data
    var d = "M", ai, ai0, ai1, bi, bd0, bd1, cp = coordPrecision;
    for (var i = 0; i < l; i++) {
      ai = a[i]; bi = b[i];
      ai0 = ai[0]; bd0 = bi[0] - ai0;
      ai1 = ai[1]; bd1 = bi[1] - ai1;
      d += " "; d += cp(ai0 + bd0 * v);
      d += " "; d += cp(ai1 + bd1 * v);
    }
    d += "Z";
    return d;
  };


  // SVG MORPH
  var getSamples = function(a, b, minPrec) { // pe, pe, lp -> saa[2] | uniformly sample max(len(a), len(b))/minPrec points in ccw winding
      var al = a.getTotalLength(), bl = b.getTotalLength(),
        ll    = (al > bl) ? al : bl, sl    = (al > bl) ? bl : al,
        l     = (al > bl) ? a : b,   s     = (al > bl) ? b : a,
        lPrec = minPrec,             sPrec = lPrec * sl / ll,
        steps = trunc[0](ll / lPrec);
      
      var handlePathElement = function(path, prec) { // pe, lp -> sa | sampling for one path element
        var curr, w, i, p, coords = new Array(steps);
        for (i = curr = w = 0; i < steps; i++, curr += prec) {
          // sample point
          p = path.getPointAtLength(curr);
          coords[i] = [ p.x, p.y ];
          // keep track of winding
          if (i) w += (coords[i][0] - coords[i-1][0]) * (coords[i][1] + coords[i-1][1]);
        }
        // last winding step
        w += (coords[0][0] - coords[steps-1][0]) * (coords[0][1] + coords[steps-1][1]);
        if (w > 0) {
          // if cw, reverse, preserving start point
          coords.reverse();
          coords = coords.slice(-1).concat(coords.slice(0, -1));
        }
        return coords;
      };

      return (al > bl)
        ? [ handlePathElement(l, lPrec), handlePathElement(s, sPrec) ]
        : [ handlePathElement(s, sPrec), handlePathElement(l, lPrec) ];
    },
    expandTools = {
        dup : 1,
        onlydup : 2,
        split: 3,
        onlysplit : 4,
        prev : function(arr, ind) { return arr[(ind - 1 + arr.length) % arr.length]; },
        next : function(arr, ind) { return arr[(ind + 1) % arr.length]; },
        dist : function(a, b) { var d0 = b[0] - a[0], d1 = b[1] - a[1]; return (d0 === 0 && d1 === 0) ? 0 : Math.sqrt(d0 * d0 + d1 * d1); },
        dwrap : function(arr, ind) { return expandTools.dist(expandTools.prev(arr, ind), arr[ind]) + expandTools.dist(arr[ind], expandTools.next(arr, ind)); },
        dnext : function(arr, ind) { return expandTools.dist(arr[ind], expandTools.next(arr, ind)); },
    },
    expandToNSamples = function(s, n, mode) { // sa, al, ... -> sa | generates n - s.length additional samples by a combination of methods. needs optimization!
      var l, r, m, ns, ord, prio, i, o, curr, next, et = expandTools, mode = mode || et.dup; 

      while (n > (l = s.length)) {
        r = n - l;        // remaining samples to generate
        m = (r < l) ? r : l; // max samples from this pass (split mode may reduce this)
        switch (mode) {
        // duplicate vertices
        case et.dup:
          mode = et.split;
        case et.onlydup:
          if (r < l) { // we can't dup everything; set priorities by sum of distances to neighboring points
            ord = new Array(l); for (i = 0; i < l; i++) ord[i] = i;
            ord.sort(function(l, r) { return et.dwrap(s, r) - et.dwrap(s, l); });
            prio = []; for (i = 0; i < l; i++) prio[ord[i]] = i;
          }
          ns = new Array(l + m);
          for (i = 0, o = 0; i < l; i++) {
            ns[o++] = curr = s[i];     // copy every time
            if (r >= l || prio[i] < r) // duplicate if needed
              ns[o++] = curr;
          }
          break;
        // split segments
        case et.split:
          mode = et.dup;
        case et.onlysplit:
          // always set priorities by distance to next point to avoid splitting 0-length segments
          ord = new Array(l); for (i = 0; i < l; i++) ord[i] = i;
          ord.sort(function(l, r) { return et.dnext(s, r) - et.dnext(s, l); });
          prio = []; for (i = 0, m = 0; i < l; i++) if (et.dnext(s, ord[i]) > 0) { prio[ord[i]] = i; m++; }
          ns = new Array(l + ((m > r) ? r : m)); // m has been modified to account for 0-length edges
          for (i = 0, o = 0; i < l; i++) {
            ns[o++] = curr = s[i];             // copy every time
            if (prio[i] > -1 && prio[i] < r) { // split if needed
              next = et.next(s, i);
              ns[o++] = [next[0] + (curr[0] - next[0]) / 2, next[1] + (curr[1] - next[1]) / 2];
            }
          }
          break;
        }
        s = ns;
      }
      return s;
    },
    pathStringToVertices = function(p) { // ps -> va | converts polygonal path string to vertex array in ccw winding
      var np = [], cc = [0, 0], lc, fc, t0, t1, e = 0, w = 0, f,
          qre = defaultQualifier,
          tre = defaultTokenizer;
      var nextToken = function() {
        var m = tre.exec(p);
        if (!m) return m;                  // no match
        if (m[1]) return m[1];             // command
        if (m[2]) return parseFloat(m[2]); // number
        if (m[3]) return m[3];             // invalid (pedanticTokenizer only)
      };
      tre.lastIndex = 0;

      if (qre.test(p)) { // if p looks like a path...
        parse: while (t0 || (t0 = nextToken())) {

          // handle command
          switch (t0) {
          case "M": case "L": e = 13; break; // x, y absolute
          case "m": case "l": e = 24; break; // x, y relative
          case "H":           e = 1; break;  // x absolute
          case "h":           e = 2; break;  // x relative
          case "V":           e = 3; break;  // y absolute
          case "v":           e = 4; break;  // y relative
          case "z": case "Z": break parse;   // end of path
          default: e = -1; break parse; // error: not a command
          }

          // handle arguments
          f = true;
          while (typeof (t0 = nextToken()) === "number"
            && (e < 10
                || typeof (t1 = nextToken()) === "number"
                  && e < 100)) {
            switch (e) {
            case 1:  cc[0]  = t0; break;
            case 2:  cc[0] += t0; break;
            case 3:               cc[1]  = t0; break;
            case 4:               cc[1] += t0; break;
            case 13: cc[0]  = t0; cc[1]  = t1; break;
            case 24: cc[0] += t0; cc[1] += t1; break;
            }

            // winding - regular term
            if (lc) w += (cc[0] - lc[0]) * (cc[1] + lc[1]);
            else fc = cc; // note first point

            // store current coordinate, mark success, iterate
            np.push(cc); f = false; lc = cc; cc = cc.slice();
          }
          if (f) break parse; // error: missing arguments
        }
      }

      // winding - last term, and normalization to ccw
      if (fc) {
        if (fc[0] === lc[0] && fc[1] === lc[1]) {
          // explicitly closed, last term is already included
          np = np.slice(0, -1); // drop duplicated point
          if (w > 0) { // if cw, reverse, preserving start point
            np.reverse();
            np = np.slice(-1).concat(np.slice(0, -1));
          }
        }
        else {
          // implicitly closed, add last term to w
          w += (fc[0] - lc[0]) * (fc[1] + lc[1]);
          if (w > 0) { // if cw, reverse, preserving start point
            np.reverse();
            np = np.slice(-1).concat(np.slice(0, -1));
          }
        }
      }
      
      // XXX error handling should go here
      if (f)
        console.log("pathStringToVertices confused: missing or malformed argument: " + p);
      else if (e === 0)
        console.log("pathStringToVertices confused: input does not look like a path: " + p);
      else if (e === -1)
        console.log("pathStringToVertices confused: path contains invalid command: " + p);
      return np;
    },
    getOnePath = function(p) { return p.split(/z/i).shift() + 'z'; }, // ps -> ps | cut path string after first closePath command
    pathStringFrom = { // se (tagname) -> ps | return a new path string from the attributes of a <tagname> element
        rect : function(e) { // FIXME units
          var x = parseFloat(e.getAttribute("x")),
              y = parseFloat(e.getAttribute("y")),
              width = parseFloat(e.getAttribute("width")),
              height = parseFloat(e.getAttribute("height")),
              rx = parseFloat(e.getAttribute("rx")),
              ry = parseFloat(e.getAttribute("ry")),
              d = "";

          if (isNaN(rx) && isNaN(ry)) rx = ry = 0;
          else if (rx > 0 && isNaN(ry)) ry = rx;
          else if (ry > 0 && isNaN(rx)) rx = ry;
          if (rx > width / 2) rx = width / 2;      
          if (ry > height / 2) rx = height / 2;

          d += "M" + (x + rx) + " " + y;
          d += "H" + (x + width - rx);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + width) + " " + (y + ry); 
          d += "V" + (y + height - ry);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + width - rx) + " " + (y + height); 
          d += "H" + (x + rx);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + x + " " + (y + height - ry); 
          d += "V" + (y + ry);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + rx) + " " + y; // SVG 2 allows dropping last coord pair before closePath
          d += "Z";

          return d;
        },
        circle : function(e) { // FIXME units
          var cx = parseFloat(e.getAttribute("cx")),
              cy = parseFloat(e.getAttribute("cy")),
              r = parseFloat(e.getAttribute("r")),
              d = "";

          d += "M" + (cx + r) + " " + cy;
          d += "A" + r + " " + r + " 0 0 1 " + cx + " " + (cy + r); // SVG spec demands 0 for sweep flag, but that makes no sense 
          d += "A" + r + " " + r + " 0 0 1 " + (cx - r) + " " + cy; 
          d += "A" + r + " " + r + " 0 0 1 " + cx + " " + (cy - r); 
          d += "A" + r + " " + r + " 0 0 1 " + (cx + r) + " " + cy; // SVG 2 allows dropping last coord pair before closePath 
          d += "Z";

          return d;
        },
        ellipse : function(e) { // FIXME units
          var cx = parseFloat(e.getAttribute("cx")),
              cy = parseFloat(e.getAttribute("cy")),
              rx = parseFloat(e.getAttribute("rx")),
              ry = parseFloat(e.getAttribute("ry")),
              d = "";

          d += "M" + (cx + rx) + " " + cy;
          d += "A" + rx + " " + ry + " 0 0 1 " + cx + " " + (cy + ry); // SVG spec demands 0 for sweep flag, but that makes no sense
          d += "A" + rx + " " + ry + " 0 0 1 " + (cx - rx) + " " + cy; 
          d += "A" + rx + " " + ry + " 0 0 1 " + cx + " " + (cy - ry); 
          d += "A" + rx + " " + ry + " 0 0 1 " + (cx + rx) + " " + cy; // SVG 2 allows dropping last coord pair before closePath 
          d += "Z";

          return d;
        },
        polygon : function(e) {
          var points = e.getAttribute("points"),
              coords, d = "";

          if (!points || /none/.test(points)) return d;

          d += "M";
          while ((coords = pathRegs.polyPointsTokenizer.exec(points))) {
            // polyPointsTokenizer matches number pairs, separated by whitespace and commas;
            // if there's an odd number of numbers, the last is ignored (complies with SVG spec)
            d += coords[1];
            d += " ";
          }
          d += "Z";
          return d;
        },
    },
    replaceWithPathElement = function(es, ep) { // se, pe -> pe (side-effects DOM) | replace non-path svgElement with svgPathElement
      var a, al, id;

      // copy non-geometry properties/attributes
      a = es.attributes;
      if (a && (al = a.length))
        for (var i = 0; i < al; i++)
          if (!/^(?:r?[xy]?|c[xy]|[xy][12]|width|height|points)$/.test(a[i].name))
            ep.setAttribute(a[i].name, a[i].value);

      // create/modify id
      if (!(id = es.id))
        id = "kutegen-" + ((Math.random() * 100000 + 99999) >> 0);
      es.id = "kuterep-" + id; ep.id = id;

      // replace
      es.parentNode.replaceChild(ep, es);

      return ep;
    },
    createPathElement = function(d) { // ps -> pe | create a naked path element with the given path string
      var p = document.createElementNS(ns, "path");
      p.setAttribute("d", d);
      return p;
    },
    ensurePathElement = function(e) { // se -> pe_OR_null | no-op for path elements, others get converted
      switch (e.tagName) {
      case "path":
        return e;
      case "glyph": // glyphs have path strings in "d"
        return createPathElement(e.getAttribute("d"));
      default:
        var psFrom = pathStringFrom[e.tagName];
        if (psFrom)
          return createPathElement(psFrom(e));
      }
      // XXX error handling
      console.log("cannot convert " + e.tagName + " to path element");
      return null;
    },
    getPathObject = function(v) { // s_OR_ps -> po | return new path object from selector or path string
      var p = {}, el;
      
      if (v) {
        if (/^[.#]/.test(v)) // looks like a selector
          el = document.querySelector(v);
        else if (pathRegs.minimalQualifier.test(v)) // looks like a path string
          el = createPathElement(v);
      }
      
      if (el) { // turn anything we know how to into a path element and build a path object from it
        if ((p.e = ensurePathElement(el))
            && (p.o = p.e.getAttribute("d"))) {
          return p;
        }
      }
      // XXX: error handling
      console.log("getPath got '" + v + "', found " + el);
      return null;
    },
    centerOfGravity = function (points) { // pa -> p | point at center of gravity of an array of points
      var cog = [0, 0], l = points.length, i;
      for (i = 0; i < l; i++) {
        cog[0] += points[i][0];
        cog[1] += points[i][1];
      }
      cog[0] /= l;
      cog[1] /= l;
      return cog;
    },
    phi = function(point, cog) { // angle between vector from cog to point, normalized to [-1..1]
      var v = [point[0] - cog[0], point[1] - cog[1]],
          phiRad = Math.atan2(v[1], v[0]); // note reversed x and y on atan2
      return phiRad / Math.PI; // normalize to [-1..1]
    },
    alignOrientation = function (start, end, impliedRotation) { // pa, pa, n -> pa | returns end, shifted to minimize phi distance of end[0] and start[0], with optional offset
      var impRot = (impliedRotation % 180) / 180,
      startCog = centerOfGravity(start),
      endCog   = centerOfGravity(end),
      startPhi = phi(start[0], startCog),
      endPhi = phi(end[0], endCog), // for testing
      l = end.length, i, d, bi, bd = Infinity;
      
      // find smallest orientation difference
      for (i = 0; i < l; i++) {
        d = Math.abs(phi(end[i], endCog) - startPhi - impRot);
        if (d < bd) {
          bd = d; bi = i;
        }
      }
      
      if (bi != 0) // unless alignment was OK, shift start vertex
        end = end.splice(bi).concat(end.splice(0, bi));

      //console.log("ir was: " + (endPhi - startPhi)*180 + " anticipated: " + impRot * 180 + " now: " + (phi(end[0], endCog) - startPhi)*180);
      return end;
    },
    computePathCross = function(s, e) { // ps, ps -> saa[2] | compute appropiate sample arrays to morph between path strings s and e
      var s_pe, e_pe, s_sa, e_sa, tmp_sa, samples,
        index = this.options.morphIndex, impRot = this.options.impliedRotation;

      if (!this._isPolygon) {
        s_pe = createPathElement(s); e_pe = createPathElement(e);
        samples = getSamples(s_pe, e_pe, this.options.morphPrecision);
        s_sa = samples[0]; e_sa = samples[1];
      }
      else {
        s_sa = pathStringToVertices(s); e_sa = pathStringToVertices(e);
        if (s_sa.length < e_sa.length)
          s_sa = expandToNSamples(s_sa, e_sa.length, expandTools.dup);
        else if (s_sa.length > e_sa.length)
          e_sa = expandToNSamples(e_sa, s_sa.length, expandTools.dup);
      }

      // reverse arrays
      if (this.options.reverseFirstPath) { s_sa.reverse(); }
      if (this.options.reverseSecondPath) { e_sa.reverse(); }

      // shift second array to for smallest tween distance
      if (index) {
        var tmp_sa = e_sa.splice(index, e_sa.length-index);
        e_sa = tmp_sa.concat(e_sa);
      }
      else { // automatic rotation
        e_sa = alignOrientation(s_sa, e_sa, impRot || 0);
      }

      return [s_sa, e_sa]
    };

  // set default morphPrecision since 1.6.1
  defaultOptions.morphPrecision = 15;

  parseProperty.path = function(o, v) { // const 'path', s_OR_ps -> po + side effects | build path object; also, verify/fix type of this.element and register the render function 
    // test eligibility for path morphing
    var e = ensurePathElement(this.element); // can we handle this?
    if (!e) return null;                     // - no, we can't
    if (e !== this.element)                  // - yes, with a conversion.
      this.element = replaceWithPathElement(this.element, e);
    
    // register render function
    if (!('path' in DOM)) {
      DOM.path = function(l, p, a, b, v) {
        l.setAttribute("d", v === 1 ? b.o : coords(a.d, b.d, b.d.length, v));
      }
    }

    // actually parse the property
    return getPathObject(v);
  };

  prepareStart.path = function(p) { // const 'path' -> ps | returns current path string of target element 
    return this.element.getAttribute('d'); 
  };

  crossCheck.path = function() { // unlike other cases, the crossCheck apply to both to() and fromTo() methods
    var p1 = getOnePath(this.valuesStart.path.o), p2 = getOnePath(this.valuesEnd.path.o), paths;

    // path tween options
    this.options.morphPrecision = this.options && 'morphPrecision' in this.options ? parseInt(this.options.morphPrecision) : defaultOptions.morphPrecision;
    this._isPolygon = !/[CSQTA]/i.test(p1) && !/[CSQTA]/i.test(p2); // check if both shapes are polygons

    // begin processing paths
    paths = computePathCross.apply(this,[p1,p2]);

    this.valuesStart.path.d = paths[0];
    this.valuesEnd.path.d = paths[1];
  };


  // SVG DRAW
  var percent = function(v,l){ return parseFloat(v) / 100 * l; },
    // SVG DRAW UTILITITES
    // http://stackoverflow.com/a/30376660
    getRectLength = function(el){ // returns the length of a Rect
      var w = el.getAttribute('width');
      var h = el.getAttribute('height');
      return (w*2)+(h*2);
    },
    getPolyLength = function(el){ // getPolygonLength / getPolylineLength - return the length of the Polygon / Polyline
      var points = el.getAttribute('points').split(' '), len = 0;
      if (points.length > 1) {
        var coord = function (p) {
          var c = p.split(',');
          if (c.length != 2) { return; } // return undefined
          if (isNaN(c[0]) || isNaN(c[1])) { return; }
          return [parseFloat(c[0]), parseFloat(c[1])];
        };

        var dist = function (c1, c2) {
          if (c1 != undefined && c2 != undefined) {
            return Math.sqrt(Math.pow((c2[0]-c1[0]), 2) + Math.pow((c2[1]-c1[1]), 2));
          }
          return 0;
        };

        if (points.length > 2) {
          for (var i=0; i<points.length-1; i++) {
            len += dist(coord(points[i]), coord(points[i+1]));
          }
        }
        len += dist(coord(points[0]), coord(points[points.length-1]));
      }
      return len;
    },
    getLineLength = function(el){ // return the length of the line
      var x1 = el.getAttribute('x1');
      var x2 = el.getAttribute('x2');
      var y1 = el.getAttribute('y1');
      var y2 = el.getAttribute('y2');
      return Math.sqrt(Math.pow((x2-x1), 2)+Math.pow((y2-y1),2));
    },
    getCircleLength = function(el){ // return the length of the circle
      var r = el.getAttribute('r');
      return 2 * Math.PI * r;
    },
    getEllipseLength = function(el) { // returns the length of an ellipse
      var rx = el.getAttribute('rx'), ry = el.getAttribute('ry'),
          len = 2*rx, wid = 2*ry;
      return ((Math.sqrt(.5 * ((len * len) + (wid * wid)))) * (Math.PI * 2)) / 2;
    },
    getTotalLength = function(el){ // returns the result of any of the below functions
      if (/rect/.test(el.tagName)) {
        return getRectLength(el);
      } else if (/circle/.test(el.tagName)) {
        return getCircleLength(el);
      } else if (/ellipse/.test(el.tagName)) {
        return getEllipseLength(el);
      } else if (/polygon|polyline/.test(el.tagName)) {
        return getPolyLength(el);
      } else if (/line/.test(el.tagName)) {
        return getLineLength(el);
      }
    },
    getDraw = function(e,v){
      var l = /path|glyph/.test(e.tagName) ? e.getTotalLength() : getTotalLength(e), start, end, d, o;
      if ( v instanceof Object ) {
        return v;
      } else if (typeof v === 'string') {
        v = v.split(/\,|\s/);
        start = /%/.test(v[0]) ? percent(v[0].trim(),l) : parseFloat(v[0]);
        end = /%/.test(v[1]) ? percent(v[1].trim(),l) : parseFloat(v[1]);
      } else if (typeof v === 'undefined') {
        o = parseFloat(getCurrentStyle(e,'stroke-dashoffset'));
        d = getCurrentStyle(e,'stroke-dasharray').split(/\,/);

        start = 0-o;
        end = parseFloat(d[0]) + start || l;
      }
      return { s: start, e: end, l: l }
    };

  parseProperty.draw = function(a,o){ // register the draw property
    if (!('draw' in DOM)) {
      DOM.draw = function(l,p,a,b,v){
        var pathLength = (a.l*100>>0)/100, start = (number(a.s,b.s,v)*100>>0)/100, end = (number(a.e,b.e,v)*100>>0)/100,
        offset = 0 - start, dashOne = end+offset;
        l.style.strokeDashoffset = offset +'px';
        l.style.strokeDasharray = (((dashOne <1 ? 0 : dashOne)*100>>0)/100) + 'px, ' + pathLength + 'px';
      }
    }
    return getDraw(this.element,o);
  }

  prepareStart.draw = function(){
    return getDraw(this.element);
  }


  // SVG Transform
  var parseStringOrigin = function(origin,box){
      return /[a-zA-Z]/.test(origin) && !/px/.test(origin) ? origin.replace(/top|left/,0).replace(/right|bottom/,100).replace(/center|middle/,50)
                                     : /%/.test(origin) ? (box.x + parseFloat(origin) * box.width / 100) : parseFloat(origin);
    },
    parseTransformString = function (a){ // helper function that turns transform value from string to object
      var d = a && /\)/.test(a) ? a.substring(0, a.length-1).split(/\)\s|\)/) : 'none', c = {};

      if (d instanceof Array) {
        for (var j=0, jl = d.length; j<jl; j++){
          var p = d[j].trim().split('('); c[p[0]] = p[1];
        }
      }
      return c;
    },
    parseTransformObject = function(v){
      var svgTransformObject = {}, bb = this.element.getBBox(),
        cx = bb.x + bb.width/2, cy = bb.y + bb.height/2, // by default the transformOrigin is "50% 50%" of the shape box
        origin = this.options.transformOrigin, translation;

      origin = !!origin ? (origin instanceof Array ? origin : origin.split(/\s/)) : [cx,cy];

      origin[0] = typeof origin[0] === 'number' ? origin[0] : parseStringOrigin(origin[0],bb);
      origin[1] = typeof origin[1] === 'number' ? origin[1] : parseStringOrigin(origin[1],bb);

      svgTransformObject.origin = origin;

      for ( var i in v ) { // populate the valuesStart and / or valuesEnd
        if (i === 'rotate'){
          svgTransformObject[i] = typeof v[i] === 'number' ? v[i] : v[i] instanceof Array ? v[i][0] : v[i].split(/\s/)[0]*1;
        } else if (i === 'translate'){
          translation = v[i] instanceof Array ? v[i] : /\,|\s/.test(v[i]) ? v[i].split(',') : [v[i],0];
          svgTransformObject[i] = [translation[0]*1||0, translation[1]*1||0];
        } else if (/skew/.test(i)) {
          svgTransformObject[i] = v[i]*1||0;
        } else if (i === 'scale'){
          svgTransformObject[i] = parseFloat(v[i])||1;
        }
      }

      return svgTransformObject;
    };

  parseProperty.svgTransform = function(p,v){
    // register the render function
    if (!('svgTransform' in DOM)) {
      DOM.svgTransform = function(l,p,a,b,v){
        var x = 0, y = 0, tmp, deg = Math.PI/180,
          scale = 'scale' in b ? number(a.scale,b.scale,v) : 1,
          rotate = 'rotate' in b ? number(a.rotate,b.rotate,v) : 0,
          sin = Math.sin(rotate*deg), cos = Math.cos(rotate*deg),
          skewX = 'skewX' in b ? number(a.skewX,b.skewX,v) : 0,
          skewY = 'skewY' in b ? number(a.skewY,b.skewY,v) : 0,
          complex = rotate||skewX||skewY||scale!==1 || 0;

        // start normalizing the translation, we start from last to first (from last chained translation)
        // the normalized translation will handle the transformOrigin tween option and makes sure to have a consistent transformation
        x -= complex ? b.origin[0] : 0; y -= complex ? b.origin[1] : 0; // we start with removing transformOrigin from translation
        x *= scale; y *= scale; // we now apply the scale
        y += skewY ? x*Math.tan(skewY*deg) : 0; x += skewX ? y*Math.tan(skewX*deg) : 0; // now we apply skews
        tmp = cos*x - sin*y; // apply rotation as well
        y = rotate ? sin*x + cos*y : y; x = rotate ? tmp : x;
        x += 'translate' in b ? number(a.translate[0],b.translate[0],v) : 0; // now we apply the actual translation
        y += 'translate' in b ? number(a.translate[1],b.translate[1],v) : 0;
        x += complex ? b.origin[0] : 0; y += complex ? b.origin[1] : 0; // normalizing ends with the addition of the transformOrigin to the translation

        // finally we apply the transform attribute value
        l.setAttribute('transform', ( x||y ? ('translate(' + (x*100>>0)/100 + ( y ? (',' + ((y*100>>0)/100)) : '') + ')') : '' )
                                    +( rotate ? 'rotate(' + (rotate*100>>0)/100 + ')' : '' )
                                    +( skewX ? 'skewX(' + (skewX*10>>0)/10 + ')' : '' )
                                    +( skewY ? 'skewY(' + (skewY*10>>0)/10 + ')' : '' )
                                    +( scale !== 1 ? 'scale(' + (scale*1000>>0)/1000 +')' : '' ) );
      }
    }

    // now prepare transform
    return parseTransformObject.call(this,v);
  }

  // returns an obect with current transform attribute value
  prepareStart.svgTransform = function(p,t) {
    var transformObject = {}, currentTransform = parseTransformString(this.element.getAttribute('transform'));
    for (var i in t) { transformObject[i] = i in currentTransform ? currentTransform[i] : (i==='scale'?1:0); } // find a value in current attribute value or add a default value
    return transformObject;
  }

  crossCheck.svgTransform = function() { // helper function that helps preserve current transform properties into the objects
    if (!this.options.rpr) return; // fix since 1.6.1 for fromTo() method
    var valuesStart = this.valuesStart.svgTransform, valuesEnd = this.valuesEnd.svgTransform,
      currentTransform = parseTransformObject.call(this, parseTransformString(this.element.getAttribute('transform')) );

    for ( var i in currentTransform ) { valuesStart[i] = currentTransform[i]; } // populate the valuesStart first

    // now try to determine the REAL translation
    var parentSVG = this.element.ownerSVGElement,
      newTransform = parentSVG.createSVGTransformFromMatrix(
        parentSVG.createSVGMatrix()
        .translate(-valuesStart.origin[0],-valuesStart.origin[1]) // - origin
        .translate('translate' in valuesStart ? valuesStart.translate[0] : 0,'translate' in valuesStart ? valuesStart.translate[1] : 0) // the current translate
        .rotate(valuesStart.rotate||0).skewX(valuesStart.skewX||0).skewY(valuesStart.skewY||0).scale(valuesStart.scale||1)// the other functions
        .translate(+valuesStart.origin[0],+valuesStart.origin[1]) // + origin
      );

    valuesStart.translate = [newTransform.matrix.e,newTransform.matrix.f]; // finally the translate we're looking for

    // copy existing and unused properties to the valuesEnd
    for ( var i in valuesStart) { if ( !(i in valuesEnd)) { valuesEnd[i] = valuesStart[i]; } }
  }

  return this;
}));