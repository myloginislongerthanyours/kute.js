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
  var ns = 'http://www.w3.org/2000/svg',
    trunc = [ // truncate to 0-2 decimal places
      function(v) { return v >> 0; },
      function(v) { return ((v * 10) >> 0) / 10; },
      function(v) { return ((v * 100) >> 0) / 100; }, ],
    round = [ // round to 0-2 decimal places
      function(v) { return Math.round(v); },
      function(v) { return Math.round(v * 10) / 10; },
      function(v) { return Math.round(v * 100) / 100; }, ],
    coordPrecision = isMobile ? trunc[0] : round[1], // use truncation on mobile, subpixel rounding on desktop
    coords = function(s, e, v) { // po, po, [0..1] -> ps | interpolation function for path data
      var d = "", a = s.d, b = e.d, l, i, po, p, pl = e.p.length, ai, bd, cp = coordPrecision;
      for (p = 0; p < pl; p++) {
        po = e.p[p];   // subpath object
        i = po.s;      // index of samples in s.d/e.d
        l = i + po.l;  // length of samples
        d += "M";
        while (i < l) { // handle subpath p
          ai = a[i]; bd = b[i] - ai; i++; // x
          d += " "; d += cp(ai + bd * v);
          ai = a[i]; bd = b[i] - ai; i++; // y
          d += " "; d += cp(ai + bd * v);
        }
        d += po.t[1 * (v >= po.tv)]; // closepath "interpolation" - adds "z" or ""
      }
      return d;
    };

  g.Interpolate.coords = isMobile ? function(a,b,l,v) { // tuned original, for export, since coords is now really specialised
    var points = new Array(l), ai, ai0, ai1, bi, bd0, bd1, i;
    for(i=0;i<l;i++) { // for each point
      ai = a[i]; bi = b[i];
      ai0 = ai[0]; bd0 = bi[0] - ai0;
      ai1 = ai[1]; bd1 = bi[1] - ai1;
      points[i] = [ (ai0 + bd0 * v) >> 0, (ai1 + bd1 * v) >> 0 ];
    }
    return points;
  } : function(a,b,l,v) { // on desktop devices we use subpixel accuracy for morph
    var points = new Array(l), ai, ai0, ai1, bi, bd0, bd1, i;
    for(i=0;i<l;i++) { // for each point
      ai = a[i]; bi = b[i];
      ai0 = ai[0]; bd0 = bi[0] - ai0;
      ai1 = ai[1]; bd1 = bi[1] - ai1;
      points[i] = [ (((ai0 + bd0 * v) * 10) >> 0) / 10, (((ai1 + bd1 * v) * 10) >> 0) / 10 ];
    }
    return points;
  };

  // SVG MORPH
  var morphRegs = {
      selectorQualifier : /^[.#]/,
      minimalPathQualifier : /^\s*m/i,
      fullPathTokenizer : /(?:\s*([acmlhqtsvz])\s*)|(?:\s*([-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?)\s*(?:,(?=\s*[-+.\d]))?)/gi,
      polyPointsTokenizer : /(?:[\s,]*((?:[-+]?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?(?:(?:\s+,?\s*)|(?:,\s*)|$)){2}))/g,
      geoPropQualifier : /^(?:r?[xy]?|c[xy]|[xy][12]|width|height|points|d)$/,
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
    expandToNSamplesOLD = function(s, n, mode) { // sa, al, ... -> sa | generates n - s.length additional samples by a combination of methods. needs optimization!
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
    matchSampleCounts = function(s, ssi, e, esi) { // po, subpath index, po, subpath index -> side effects on shorter (in samples) subpath | duplicates vertices or splits segments
      var source = s.p[ssi], target = e.p[ssi], plan, smaller, larger, sdiff, vdiff,
      i, o,
      et = expandTools;
      
      if (source.ss.length < target.ss.length) {
        smaller = source; larger = target;
        plan = (source.vs.length < target.vs.length) ? et.split : et.dup;
      }
      else if (source.ss.length > target.ss.length) {
        smaller = target; larger = source;
        plan = (source.vs.length > target.vs.length) ? et.dup : et.split; 
      }
      else return; // there's nothing to do.
      
      sdiff = (larger.ss.length - smaller.ss.length);

      // HAH
      plan = et.dup;
      
      // simplest possible implementation, to be fixed later.
      switch (plan) {
      case et.dup:
        for (i = 0, o = 0; i < smaller.vs.length; i++) {
          smaller.vs[i][2] += o;
          if (i < sdiff) {
            smaller.ss.splice(smaller.vs[i][2], 0, smaller.ss[smaller.vs[i][2]]);
            o++
          }
          
          // sanity check:
          if (!(smaller.vs[i][0] === smaller.ss[smaller.vs[i][2]][0] && smaller.vs[i][1] === smaller.ss[smaller.vs[i][2]][1])) {
            console.log("dup not working correctly: " + i);
            return;
          }
        }
        // reevaluate
        matchSampleCounts(s, ssi, e, esi);
        break;
      case et.split:
        break;
      }
      
    },
    createSubpathObjects = function(po, minPrec) { // po, samplePrecision -> (po update) | creates subpath objects on po for all subpaths, using adaptive sampling
      var input = po.o,
      MAX_ARGS = 7, N_ACCS = 13, MIN_SEGMENT = 2,
      ivx, ivy, c, dx, dy, sy, hx, hy, tx, ty,
      polySegLen, currPolyLen, pathSegLen, currPathLen, samplePE, samplePS, spsp, spsl,
      accept = [], queue, cand, mid,
      ct, cc, nc, ca = new Array(MAX_ARGS), cna = 0, tpl, i, is = 0,
      qre = morphRegs.minimalPathQualifier,
      tre = morphRegs.fullPathTokenizer;
      
      // command properties: c:  normalised command char,
      //                     t:  type (1: line, 2: smooth curve, 3: full curve, -1: m, -2: z),
      //                     pc: parameter control 0-1 xy, 2-3 quad cp, 4-6 cube cp, 8-12 arc params
      //                     l:  accumulation length, a: absolute flag
      var commands = {
          H: { c: "H", t:  1, pc: [0],                      l: 2, a: true  }, 
          h: { c: "H", t:  1, pc: [0],                      l: 2, a: false }, 
          V: { c: "V", t:  1, pc: [1],                      l: 2, a: true  }, 
          v: { c: "V", t:  1, pc: [1],                      l: 2, a: false }, 
          L: { c: "L", t:  1, pc: [0, 1],                   l: 2, a: true  }, 
          l: { c: "L", t:  1, pc: [0, 1],                   l: 2, a: false }, 
          T: { c: "Q", t:  2, pc: [0, 1],                   l: 4, a: true  }, 
          t: { c: "Q", t:  2, pc: [0, 1],                   l: 4, a: false }, 
          Q: { c: "Q", t:  3, pc: [2, 3, 0, 1],             l: 4, a: true  }, 
          q: { c: "Q", t:  3, pc: [2, 3, 0, 1],             l: 4, a: false }, 
          S: { c: "C", t:  2, pc: [6, 7, 0, 1],             l: 8, a: true  }, 
          s: { c: "C", t:  2, pc: [6, 7, 0, 1],             l: 8, a: false }, 
          C: { c: "C", t:  3, pc: [4, 5, 6, 7, 0, 1],       l: 8, a: true  }, 
          c: { c: "C", t:  3, pc: [4, 5, 6, 7, 0, 1],       l: 8, a: false }, 
          A: { c: "A", t:  3, pc: [8, 9, 10, 11, 12, 0, 1], l: 2, a: true  }, 
          a: { c: "A", t:  3, pc: [8, 9, 10, 11, 12, 0, 1], l: 2, a: false }, 
          M: { c: "M", t: -1, pc: [0, 1],                         a: true  }, 
          m: { c: "M", t: -1, pc: [0, 1],                         a: false }, 
          Z: { c: "z", t: -2, pc: [],                                      }, 
          z: { c: "z", t: -2, pc: [],                                      }, 
      };

      var nextToken = function() {
        var m = tre.exec(input);
        if (!m) { input = null; return m; } // no match, stop tokenizer
        if (m[1]) return commands[m[1]];    // command
        if (m[2]) return parseFloat(m[2]);  // number
      };
      tre.lastIndex = 0;
      
      if (qre.test(input) && (ct = nextToken())) {
        po.p = [];
        
        //
        // command loop
        //
        commands: while (ct && typeof ct === "object") {
          cc = ct;
          cna = cc.pc.length;
          is = 0;
          //
          // argument loop
          //
          arguments: do {
            for (i = is, is = 0; i < cna; i++)
              if (typeof (ca[i] = nextToken()) !== "number")
                throw new Error("path string has missing or malformed arguments");
            
            //
            // case 1: start a new subpath (moveto command or first subpath)
            //
            if (!c || cc.t === -1) {
              // check preconditions
              if (po.p.length === 0 && cc.t !== -1) throw new Error("path string does not start with moveto command");
              if (cc.t === 5) throw new Error("path string contains empty subpath");

              // handle moveto, part 1
              if (cc.t === -1) {
                if (po.p.length === 0) { // start from 0,0
                  ivx = ivy = 0;
                }
                else { // start from last current point
                  c = c || po.p[po.p.length - 1]; // resurrect c for a moment
                  ivx = c._h[0];
                  ivy = c._h[1];
                }
                ivx = cc.a ? ca[0] : ivx + ca[0];
                ivy = cc.a ? ca[1] : ivy + ca[1];
              }
            
              // start new subpath
              po.p.push(c = {
                s  : -1, // sample start in overall path (set in crossCheck)
                l  : -1, // sample length in overall path (set in crossCheck)
                t  : ["", ""], // open/closed (interpolation values < tv, >= tv, starts open, closed by closepath)
                tv : -1, // no opening/closing during interpolation (can be changed in crossCheck)
                vs : [[ivx, ivy, 0]], // vertex/sample index array
                ss : [[ivx, ivy]],    // sample array
                w  : 0,          // winding accumulator (handled by closepath)
                c  : [ivx, ivy], // center of gravity accumulator (handled in crossCheck)
                p  : 0,          // phi (calculated in crossCheck)
                _h : new Array(N_ACCS), // accummulators used while building this subpath
                _t : null,
              });
              c._h[0] = ivx; c._h[1] = ivy;
              currPolyLen = 0; currPathLen = 0; tpl = -1;
              samplePS = "M" + ivx + " " + ivy + " ";
              
              // handle moveto, part 2
              if (cc.t === -1) {
                cc = cc.a ? commands.L : commands.l; // masquerade as a lineto of correct relativity
                continue arguments;
              }
            }
            
            //
            // case 2: closepath command
            //
            if (cc.t === -2) {
              c.t[0] = c.t[1] = "z"; // mark subpath closed
              if (ivx !== c._h[0] && ivy !== c._h[1])
                c.w += (ivx - c._h[0]) * (ivy + c._h[1]); // finish winding
              c = null; // see you in crossCheck ;)
              
              // if there are more tokens...
              if ((ct = nextToken()) && typeof ct === "object")
                continue commands;
              else if (typeof ct === "number")
                throw new Error("path string has numbers after closepath command");
              else
                break commands; // we're done with the entire path string
            }
            
            //
            // case 3: drawing commands
            //
            //   - step 1: getting to _t(here) from _h(ere)
            c._t = c._h.slice(0, cc.l);                              // relevant accumulators
            if (cc.l == 8 && c._t[2]) c._t[2] = c._t[3] = undefined; // special case: kill quad spline accumulator. 
            for (i = 0; i < cna; i++)
              c._t[cc.pc[i]] = (cc.a ? ca[i]                         // update from current arguments
                                     : c._t[cc.pc[i] % 2] + ca[i]);  // relative to current point

            //   - step 2: vertex updates
            hx = c._h[0]; hy = c._h[1]; tx = c._t[0]; ty = c._t[1];  // old and new absolute vertices.
            c.c[0] += tx; c.c[1] += ty;                              // add to cog accumulation.
            dx = tx - hx; dy = ty - hy; sy = ty + hy;                // get deltas and sum
            polySegLen = Math.sqrt(dx * dx + dy * dy);               // for length, and
            c.w += dx * sy;                                          // for winding.
            
            //   - step 3: handle smooth control points
            nc = commands[cc.c];                                     // get normalized command.
            if (cc.t === 2) {
              var ofs = (nc.l - 4) / 2;                              // FIXME annoying offset (S vs. T)
              if (typeof c._h[nc.pc[ofs]] === "number") {            // there is a previous control point,
                c._t[nc.pc[0]] = hx + (hx - c._h[nc.pc[ofs]]);       // so reflect it
                c._t[nc.pc[1]] = hy + (hy - c._h[nc.pc[ofs+1]]);     // across the last vertex.
              }
              else c._t[nc.pc[0]] = hx; c._t[nc.pc[1]] = hy;         // use the last vertex itself.
            }
            
            //   - step 4: find the right amount of samples
            //
            //       - case a: straight line -> one sample
            if (cc.t === 1) {
              c.vs.push([tx, ty, c.ss.length]);                      // store current vertex.
              c.ss.push([tx, ty]);                                   // store current sample.
              currPolyLen += polySegLen; currPathLen += polySegLen;  // update total lengths.
              samplePS += nc.c;                                      // update sample path string with
              for (i = 0; i < nc.pc.length; i++) {                   // normalized command and all
                samplePS += c._t[nc.pc[i]]; samplePS += " ";         // parameters.
              }
              c._h = c._t; c._t = null;                              // flip accumulators.
              continue arguments;                                    // done.
            }
            
            //       - case b: not a straight line.
            //
            //         TODO: could test control points / parameters here to avoid
            //               sampling obviously straight lines.
            if (!samplePE || tpl == -1) {
              if (!samplePE) samplePE = createPathElement(samplePS); // get a path element
              else samplePE.setAttribute("d", samplePS);             // set up correctly, and
              tpl = samplePE.getTotalLength();                       // calibrated.
              if (currPathLen - tpl > 0.01)
                console.log("Warning: length calc problem. " + currPathLen + " !== " + tpl);
              currPathLen = tpl;
            }

            spsp = "M" + hx + " " + hy + " ";         // path string prefix for current position
            spsl = nc.c;                              // build a path string from the current
            for (i = 0; i < nc.pc.length; i++) {      // normalized command and all
              spsl += c._t[nc.pc[i]]; spsl += " ";    // parameters.
            }
            samplePS += spsl;                         // add it to samplePS for future reference
            samplePE.setAttribute("d", spsp + spsl);  // set up samplePE with local prefix, and
            pathSegLen = samplePE.getTotalLength();   // measure it.

            //
            // adaptive sampling loop
            //
            // start the queue with the current segment.
            queue = [ { s: [hx, hy], e: [tx, ty], off: 0, pol: polySegLen, pal: pathSegLen } ];
            do {
              cand = queue.shift();
              // pol^2 must be at least minPrec % of pal^2
              // or less than MIN_SEGMENT (default: 2. IMPORTANT! Only you can prevent infinite loops. ;) )
              if (minPrec < (100 - (cand.pal * cand.pal - cand.pol) * 100 / (cand.pal * cand.pal))
                  || cand.pol < MIN_SEGMENT) { 
                accept.push(cand);
              }
              else { // split it up
                mid = samplePE.getPointAtLength(cand.off + cand.pal / 2);
                queue.push( {
                    s:   cand.s,
                    e:   [mid.x, mid.y],
                    off: cand.off,
                    pol: Math.pow(cand.s[0] - mid.x, 2) + Math.pow(cand.s[1] - mid.y, 2),
                    pal: cand.pal / 2 },
                  {
                    s:   [mid.x, mid.y],
                    e:   cand.e,           
                    off: cand.off + cand.pal / 2,
                    pol: Math.pow(cand.e[0] - mid.x, 2) + Math.pow(cand.e[1] - mid.y, 2),
                    pal: cand.pal / 2 } );
              }
            } while (queue.length > 0);
            
            accept.sort(function(l, r) { return l.off - r.off; }); // order by offset
            while ((cand = accept.shift()))
              c.ss.push([cand.e[0], cand.e[1]]);         // store samples.
            c.vs.push([tx, ty, c.ss.length - 1]);        // store vertex (at last sample).
            currPathLen += pathSegLen;                   // update lengths.
            currPolyLen += pathSegLen;
            c._h = c._t; c._t = null;                    // flip accumulators, and done.
            
          } while (typeof (ca[is++] = nextToken()) === "number"); // end of argument loop

          // don't lose that command if there was one.
          ct = ca[is - 1]; is = 0;
          
        } // end of command loop
        
        // normalize everything
        normalizePathObject(po);
        
      } // end of qualifying condition
    },
    normalizePathObject = function(po) { // po -> update po | set/correct cog, phi, winding, length 
      // TODO not implemented yet
      // relevant aspects:
      //   - vertices:
      //       - general sanity (? config?)
      //       - vertex on first sample present
      //       - vertex on last sample present (open) / NOT present (closed)
      //   - metrics
      //       - po length (path + poly) XXX collect in cspo
      //       - po area (for open, too - good indicator for closing time)
      //       - cogs per po and overall. sample cog??
      //       - phi per po
      //   - additional fixups
      //       - normalize winding (configurable?)
    },
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
          else if (rx >= 0 && isNaN(ry)) ry = rx;
          else if (ry >= 0 && isNaN(rx)) rx = ry;
          if (rx > width / 2) rx = width / 2;      
          if (ry > height / 2) ry = height / 2;

          d += "M" + (x + rx) + " " + y;
          d += "H" + (x + width - rx);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + width) + " " + (y + ry); 
          d += "V" + (y + height - ry);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + width - rx) + " " + (y + height); 
          d += "H" + (x + rx);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + x + " " + (y + height - ry); 
          d += "V" + (y + ry);
          if (rx * ry > 0) d += "A" + rx + " " + ry + " 0 0 1 " + (x + rx) + " " + y; // SVG 2 allows dropping last coord pair before closePath
          d += "z";

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
          d += "z";

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
          d += "z";

          return d;
        },
        line: function(e) { // FIXME units
          var x1 = parseFloat(e.getAttribute("x1")),
              y1 = parseFloat(e.getAttribute("y1")),
              x2 = parseFloat(e.getAttribute("x2")),
              y2 = parseFloat(e.getAttribute("y2")),
              d = "";
       
          d += "M" + x1 + " " + y1 + " " + x2 + " " + y2;
          
          return d;
        },
        polyline : function(e) {
          var points = e.getAttribute("points"),
              coords, d = "";

          if (!points || /none/.test(points)) return d;

          d += "M";
          while ((coords = morphRegs.polyPointsTokenizer.exec(points))) {
            // polyPointsTokenizer matches number pairs, separated by whitespace and commas;
            // if there's an odd number of numbers, the last is ignored (complies with SVG spec)
            d += coords[1];
            d += " ";
          }
          return d;
        },
        polygon : function(e) { // just a closed polyline
          var d = pathStringFrom.polyline(e);

          if (d !== "")
            d += "z";

          return d;
        },
    },
    replaceWithPathElement = function(es, ep) { // se, pe -> pe + (DOM side-effects) | replace non-path svgElement with svgPathElement
      var a, al, id;

      // copy non-geometry properties/attributes
      a = es.attributes;
      if (a && (al = a.length))
        for (var i = 0; i < al; i++)
          if (!morphRegs.geoPropQualifier.test(a[i].name)) // TODO: factor out
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
    ensurePathElement = function(e) { // se -> pe_OR_null | no-op for path elements, others get converted if possible
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
    createPathObject = function(v, minPrec) { // s_OR_ps -> po | return new path object from selector or path string, sampling at minPrec
      var p = {}, el;
      
      if (v) {
        if (morphRegs.selectorQualifier.test(v)) // looks like a selector
          el = document.querySelector(v);
        else if (morphRegs.minimalPathQualifier.test(v)) // looks like a path string
          el = createPathElement(v);
      }
      
      if (el) { // turn anything we know how to into a path element and build a path object from it
        if ((p.e = ensurePathElement(el))
            && (p.o = p.e.getAttribute("d"))) {
          createSubpathObjects(p, minPrec);
          return p;
        }
      }
      // XXX: error handling
      console.log("createPathObject got '" + v + "', found " + el);
      return null;
    },
    flattenPathObjects = function() { // po+ -> each po side effects | dump subpath objects into d, empty ss
      var csp, i, spo, p, a, argc = arguments.length;
      
      for (a = 0; a < argc; a++) {
        p = arguments[a];
        csp = 0;
        p.d = [];
        for (i = 0; i < p.p.length; i++) {
          spo = p.p[i];
          spo.l = spo.ss.length * 2;
          spo.s = csp;
          while (spo.ss.length > 0)
            Array.prototype.push.apply(p.d, spo.ss.shift());

          csp += spo.l
        }
      }
    },
    phi = function(p, c) { // angle between vector from cog to point, normalized to [-1..1]
      return Math.atan2(p[1] - c[1], p[0] - c[0]) / Math.PI; // note reversed x and y on atan2 
    },
    alignOrientationOLD = function (start, end, impliedRotation) { // pa, pa, n -> pa | returns end, shifted to minimize phi distance of end[0] and start[0], with optional offset
      var impRot = (impliedRotation % 180) / 180,
      startCog = [0, 0], // centerOfGravity(start),
      endCog   = [0, 0], // centerOfGravity(end),
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

      return end;
    },
    computePathCross = function(s, e) { // po, po -> updated po, po | update sample arrays to morph between path objects s and e
      var p, index = this.options.morphIndex, impRot = this.options.impliedRotation;

      // if the shape of the end element changed after it was parsed, get a new instance
      // not doing this will mess up sampling on to()-tweens that have their target as their end state
      if (e.e === this.element && e.e.getAttribute("d") !== e.o)
        e.e = createPathElement(e.o);

      // XXX missing: subpath mapping
      // for now: either the subpath counts match, or we only deal with subpath 0
      if (s.p.length !== e.p.length) s.p.length = e.p.length = 1;
      for (p = 0; p < e.p.length; p++)
        matchSampleCounts(s, p, e, p);
      
      // XXX missing:
      //   - force reverse
      //   - index / autorotate
      
      // get ready to draw
      flattenPathObjects(s, e);
    };

    
  // set default options since 1.6.1
  defaultOptions.morphPrecision = 15; // uniform sampling: max path length between samples, in pixels
  defaultOptions.samplePrecision = 99.5; // adaptive sampling: min polyline length as a percentage of corresponding spline/arc length  

  parseProperty.path = function(o, v) { // const 'path', s_OR_ps -> po + side effects | build path object; also, verify/fix type of this.element and register the render function 
    // test eligibility for path morphing
    var e = ensurePathElement(this.element); // can we handle this?
    if (!e) return null;                     // - no, we can't
    if (e !== this.element)                  // - yes, with a conversion.
      this.element = replaceWithPathElement(this.element, e);
    
    // register render function
    if (!('path' in DOM)) {
      DOM.path = function(l, p, a, b, v) {
        l.setAttribute("d", v === 1 ? b.o : coords(a, b, v));
      }
    }

    // pick up relevant options
    this.options.samplePrecision = this.options && 'samplePrecision' in this.options ? parseFloat(this.options.samplePrecision) : defaultOptions.samplePrecision;
    if (this.options.samplePrecision > 99.99) this.options.samplePrecision = 99.99;
    if (this.options.samplePrecision < 0.01) this.options.samplePrecision = 0.01;
    
    // actually parse the property
    return createPathObject(v, this.options.samplePrecision);
  };

  prepareStart.path = function(p) { // const 'path' -> ps | returns current path string of target element 
    return this.element.getAttribute('d'); 
  };

  crossCheck.path = function() { // unlike other cases, the crossCheck apply to both to() and fromTo() methods
    var s = this.valuesStart.path, e = this.valuesEnd.path;

    // path tween options
    this.options.morphPrecision = this.options && 'morphPrecision' in this.options ? parseInt(this.options.morphPrecision) : defaultOptions.morphPrecision;

    // begin processing paths
    computePathCross.call(this, s, e);
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