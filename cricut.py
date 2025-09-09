import sys, re, math, time
import numpy as np
from svgpathtools import svg2paths2
import xml.etree.ElementTree as ET
from svgpathtools import parse_path
import matplotlib.pyplot as plt
from typing import List


cricut_dps = 404.4
in_per_user = 116.6667



import random, math, serial
try:
    import xxtea
except:
    print("failed to import")
    xxtea = None


def MX(z, y, s, k, p, e):
    return (( ( z >> 5 ) ^ ( y << 2 )) + ( ( y >> 3 ) ^ ( z << 4 ) ) ) ^ ( ( s ^ y ) + ( k[ ( p & 3 ) ^ e ] ^ z ))

def btea( p, n, k_in ):
    v = p.copy()
    status = 2
    word_count = 0

    if( n >= 0 ):
        word_count = n
    else:
        word_count = -1*n

    k = k_in.copy()

    DELTA=0x9e3779b9
    MASK=0xFFFFFFFF

    if( word_count == 0 ):
        return 1

    #Init variables
    #p = 0
    #q = 0
    e = 0
    z   = v[ word_count - 1 ]
    y   = v[ 0 ]
    s   = 0

    #The core of the algorithm
    #define MX() ( ( ( z >> 5 ) ^ ( y << 2 )) + ( ( y >> 3 ) ^ ( z << 4 ) ) ) ^ ( ( sum ^ y ) + ( k[ ( p & 3 ) ^ e ] ^ z ) )

    if ( n > 1 ):
        q = 6 + (52 // word_count)
        while ( q > 0 ):
            q -= 1
            s = (s+DELTA) & MASK
            e = (s >> 2)&3 
            lp = 0
            for p in range(0, word_count-1):
                y = v[p+1]

                v[p] = (v[p] + ((( ( z >> 5 ) ^ ( y << 2 )) + ( ( y >> 3 ) ^ ( z << 4 )) ) ^ ( ( s ^ y ) + ( k[ ( p & 3 ) ^ e ] ^ z ))))&MASK
                z = v[p]
                lp = p
            y = v[0]
            
            lp += 1
            v[ word_count - 1 ] = (v[word_count - 1] + ((( ( z >> 5 ) ^ ( y << 2 )) + ( ( y >> 3 ) ^ ( z << 4 )) ) ^ ( ( s ^ y ) + ( k[ ( lp & 3 ) ^ e ] ^ z ))))&MASK
            

            
            z = v[ word_count - 1 ]
            
        status = 0
    #else if ( n <-1 ):
    #{
    #    /* Decoding Part */
    #    q = 6 + 52 / word_count ;
    #    sum = q * DELTA ;
    #    while (sum != 0)
    #    {
    #        e = sum>>2 & 3 ;
    #        for (p = word_count - 1 ; p > 0 ; p-- )
    #        {
    #            z = v[p-1];
    #            y = v[p] -= MX();
    #        }
    #        z = v[ word_count -1 ] ;
    #        y = v[0] -= MX();
    #        sum -= DELTA ;
    #    }
    #    status = 0;
    #}
    return v




class Cutter(serial.Serial):
    # Constants for cmd40
    CutLine = 0
    CutCurve = 1
    MoveTo = 2
    LowerAndCutLine = 3
    CutLineAndRaise = 4
    LowerAndCutCurve = 5
    CutCurveAndRaise = 6
    DecryptKey = 7

    # XXTEA encryption keys
    KEY0 = [ 0x27, 0x2D, 0x6C, 0x37, 0x34, 0x2A, 0x61, 0x73, 0x36, 0x63, 0x25, 0x5B, 0x2B, 0x26, 0x5A, 0x4D ]
    KEY1 = [ 0x7D, 0x31, 0x6E, 0x22, 0x4A, 0x4A, 0x71, 0x33, 0x5A, 0x3C, 0x5C, 0x5F, 0x78, 0x61, 0x3A, 0x61 ]
    KEY2 = [ 0x47, 0x30, 0x2A, 0x23, 0x5D, 0x31, 0x48, 0x2F, 0x3B, 0x25, 0x7A, 0x61, 0x36, 0x71, 0x38, 0x2F ]
    KEY3 = [ 0x30, 0x3F, 0x68, 0x63, 0x71, 0x64, 0x6D, 0x30, 0x47, 0x69, 0x45, 0x7B, 0x6D, 0x34, 0x25, 0x69 ]
    KEY4 = [ 0x45, 0x35, 0x66, 0x50, 0x3A, 0x38, 0x6D, 0x69, 0x57, 0x5A, 0x70, 0x37, 0x33, 0x5F, 0x35, 0x7D ]
    KEY5 = [ 0x34, 0x3A, 0x21, 0x48, 0x61, 0x4F, 0x39, 0x25, 0x75, 0x3F, 0x69, 0x53, 0x47, 0x46, 0x36, 0x26 ]
    KEY6 = [ 0x3F, 0x62, 0x62, 0x6D, 0x7E, 0x55, 0x5F, 0x44, 0x7E, 0x29, 0x42, 0x5A, 0x52, 0x24, 0x62, 0x68 ]
    KEY7 = [ 0x47, 0x30, 0x2A, 0x23, 0x34, 0x2A, 0x61, 0x73, 0x47, 0x69, 0x45, 0x7B, 0x33, 0x5F, 0x35, 0x7D ]
    keys = (KEY0,KEY1,KEY2,KEY3,KEY4,KEY5,KEY6,KEY7)
    
    WKEY0 = [ 0x272D6C37, 0x342A6173, 0x3663255B, 0x2B265A4D ]
    WKEY1 = [ 0x7D316E22, 0x4A4A7133, 0x5A3C5C5F, 0x78613A61 ]
    WKEY2 = [ 0x47302A23, 0x5D31482F, 0x3B257A61, 0x3671382F ]
    WKEY3 = [ 0x303F6863, 0x71646D30, 0x4769457B, 0x6D342569 ]
    WKEY4 = [ 0x45356650, 0x3A386D69, 0x575A7037, 0x335F357D ]
    WKEY5 = [ 0x343A2148, 0x614F3925, 0x753F6953, 0x47463626 ]
    WKEY6 = [ 0x3F62626D, 0x7E555F44, 0x7E29425A, 0x52246268 ]
    WKEY7 = [ 0x47302A23, 0x342A6173, 0x4769457B, 0x335F357D ]
    key_words = (WKEY0,WKEY1,WKEY2,WKEY3,WKEY4,WKEY5,WKEY6,WKEY7)

    # Internal storage
    _model = None
    _verMaj = None
    _verMin = None
    
    def mkstr(*l):
        if type(l[0]) == list or type(l[0]) == tuple:
            l = l[0]
        rv = str()
        for i in l: rv += chr(i)
        return rv
        

    def cmd(self, data, check_return=True):
        """Writes a command to the device. The length will be calculated from the input, so do not include a length byte."""
        data.insert(0, len(data))
        print(data)
        self.write(data)
        if check_return:
            back = self.read(1)
            print(back)
            if len(back) > 0:
                rlen = ord(back)
                rv = self.read(rlen)
                return rv
    def cmd40(self, c, x, y):
        """Writes an 0x40 command to the device. The first parameter is one of Cutter.CutLine, Cutter.CutCurve, Cutter.MoveTo,
           Cutter.LowerAndCutLine, Cutter.CutLineAndRaise, Cutter.LowerAndCutCurve, Cutter.CutCurveAndRaise, or Cutter.DecryptKey.
           The second and third parameters are the X and Y coordinates of the command."""
        if xxtea is None:
            raise NotImplementedError()
        r = random.randint(10000,32767)
        
        
        write_data = bytearray([13, 0x40])
        plaintext = bytearray([0, 0, int(r/256)%256, int(r%256), 0, 0, int(y/256)%256, int(y%256), 0, 0, int(x/256)%256, x%256])
        
        cipher = []
        for i in range(0, 3):
            cipher.append(int.from_bytes(plaintext[(i*4):(i*4)+4], byteorder='big'))
        #
        cipher = btea(cipher, 3, self.key_words[c])

        formatted = []
        for i in cipher:
            write_data.extend(i.to_bytes(4, byteorder='little'))
        
        write_data.extend(formatted)

        self.write(write_data)
        try:
            rlen = self.read(1)
            back = self.read(ord(rlen))
            print(back.hex())
            return back
        except:
            return None
        
    def bounds(self):
        """Returns the mat bounds as (xmin, ymin, xmax, ymax)."""
        b = [ord(ch) for ch in self.cmd(bytearray([0x11,0,0,0]))]
        return b[0]*256+b[1], b[2]*256+b[3], b[4]*256+b[5], b[6]*256+b[7]
    def hasMat(self):
        """Returns True if a mat is loaded, False otherwise."""
        b = self.cmd(bytearray([0x14,0,0,0,0]))
        return ord(b[3]) & 0x01 and True or False
    def _cacheModel(self):
        #b = [ord(ch) for ch in ]
        b = self.cmd(bytearray([0x12]))
        self._model = b[0]*256+b[1]
        self._verMaj = b[2]*256+b[3]
        self._verMin = b[4]*256+b[5]
    def model(self):
        """Returns the model ID of the device."""
        if self._model is None:
            self._cacheModel();
        return self._model
    def version(self):
        """Returns the firmware version of the device."""
        if self._model is None:
            self._cacheModel();
        return self._verMaj + self._verMin * math.pow(10, -math.ceil(math.log(self._verMin,10)))

def get_all_path_d_attributes(svg_file):
    """
    Extract every 'd' attribute from <path> elements in the SVG.
    """
    tree = ET.parse(svg_file)
    root = tree.getroot()
    # Handle default namespace if present
    ns = {}
    if root.tag.startswith('{'):  
        uri = root.tag.split('}')[0].strip('{')
        ns = {'svg': uri}

    # Find all path tags, namespaced or not
    paths = root.findall('.//{0}path'.format('svg:' if ns else ''), ns)
    for elem in paths:
        d = elem.get('d')
        if d:
            yield d

def compute_svg_bbox(svg_file):
    """
    Returns (min_x, min_y, max_x, max_y) across all paths.
    """
    min_x = float('inf')
    min_y = float('inf')
    max_x = -float('inf')
    max_y = -float('inf')

    for d in get_all_path_d_attributes(svg_file):
        path = parse_path(d)
        # Path.bbox() → (xmin, xmax, ymin, ymax)
        xmin, xmax, ymin, ymax = path.bbox()
        min_x = min(min_x, xmin)
        min_y = min(min_y, ymin)
        max_x = max(max_x, xmax)
        max_y = max(max_y, ymax)

    if min_x == float('inf'):
        raise RuntimeError("No <path> elements with 'd' found in SVG.")

    return min_x, min_y, max_x, max_y


def parse_length(length_str):
    """
    Convert an SVG length like '800px', '50%', or '10cm' into a float and unit.
    Returns (value: float, unit: str).
    """
    import re
    m = re.match(r'([0-9.]+)([a-zA-Z%]*)', length_str)
    if not m:
        raise ValueError(f"Invalid length: {length_str}")
    value, unit = m.groups()
    return float(value), unit

def get_svg_size(svg_path):
    # 1. Load and find root <svg>
    tree = ET.parse(svg_path)
    root = tree.getroot()

    # 2. Attempt to read width/height attributes
    w_attr = root.get("width")
    h_attr = root.get("height")
    if w_attr and h_attr:
        w_val, w_unit = parse_length(w_attr)
        h_val, h_unit = parse_length(h_attr)
        return {"width": w_val, "width_unit": w_unit,
                "height": h_val, "height_unit": h_unit}

    # 3. Fallback to viewBox: "minX minY width height"
    viewbox = root.get("viewBox") or root.get("viewbox")
    if viewbox:
        minx, miny, w, h = map(float, viewbox.strip().split())
        return {"width": w, "width_unit": None,
                "height": h, "height_unit": None}

    # 4. No size info found
    raise RuntimeError("SVG has no width/height or viewBox attributes")

def euclidean_distance(p1, p2):
    """
    p1, p2: tuples or lists like (x, y)
    Returns the Euclidean distance between p1 and p2.
    """
    dx = p2[0] - p1[0]
    dy = p2[1] - p1[1]
    return math.hypot(dx, dy)   # sqrt(dx**2 + dy**2)



def trace_svg(filename, samples_per_path=100, width=6, height=12):
    """
    Load an SVG, sample each path at uniform intervals,
    and print out the (x, y) coordinates.
    """

    paths, attributes, _ = svg2paths2(filename)
    print(attributes)
    points = []
    
    for idx, path in enumerate(paths):
        # Optional: grab the element’s id or use index as label
        elem_id = attributes[idx].get("id", f"path_{idx}")
        print(f"\n# Path {idx} (id={elem_id}):")

        # sample t from 0→1
        for t in np.linspace(0, 1, samples_per_path):
            pt = path.point(t)
            
            points.append((int(pt.real/in_per_user*cricut_dps), int(pt.imag/in_per_user*cricut_dps)))
            print(f"{int(pt.real/in_per_user*cricut_dps):.3f}, {int(pt.imag/in_per_user*cricut_dps):.3f}")
    
    #for p in points:
    #    plt.scatter(p[0], p[1])
    #
    #plt.title(f"Traced Points from '{svg_file}'")
    #plt.xlabel('X (user units)')
    #plt.ylabel('Y (user units)')
    #plt.legend(markerscale=4, fontsize='small', ncol=2)
    #plt.tight_layout()
    #plt.show()
    #
    vector_set = [[points[0]]]
    for p in range(1, len(points)):
        #relative_diff = abs((ponts[p-1] - points[p])/points[p])*100
        avg = (points[p][0] + points[p][1])/2
        print(euclidean_distance(points[p-1], points[p]), avg, "-")
        
        if euclidean_distance(points[p-1], points[p]) < 200 :
            vector_set[-1].append(points[p])
        else:
            vector_set.append([points[p]])

    #print(len(vector_set))
    #for v in vector_set:
    #    print(len(v))
    #    for p in v:
    #        plt.scatter(p[0], p[1])
    #
    #    plt.title(f"Traced Points from '{svg_file}'")
    #    plt.xlabel('X (user units)')
    #    plt.ylabel('Y (user units)')
    #    plt.legend(markerscale=4, fontsize='small', ncol=2)
    #    plt.tight_layout()
    #    plt.show()

    return vector_set
            
        
def trace_svg_points(svg_file, samples_per_path=200):
    """
    Parse an SVG file and return a list of (x, y) arrays,
    one pair per path.
    """
    paths, attributes, _ = svg2paths2(svg_file)
    all_xy = []

    for idx, path in enumerate(paths):
        # sample t from 0→1 uniformly
        ts = np.linspace(0, 1, samples_per_path)
        xs = np.empty_like(ts)
        ys = np.empty_like(ts)

        for i, t in enumerate(ts):
            pt = path.point(t)
            xs[i] = pt.real
            ys[i] = pt.imag

        all_xy.append((xs, ys))

    return all_xy

def plot_svg_points(svg_file, samples_per_path=200):
    """
    Trace the SVG outlines and scatter-plot each path in a distinct color.
    """
    all_xy = trace_svg_points(svg_file, samples_per_path)

    plt.figure(figsize=(8, 6))
    cmap = plt.get_cmap('tab20')

    for idx, (xs, ys) in enumerate(all_xy):
        plt.scatter(xs, ys,
                    s=2,
                    color=cmap(idx % cmap.N),
                    label=f'Path {idx}')

    plt.gca().invert_yaxis()                # SVG origin is top-left
    plt.gca().set_aspect('equal', 'box')    # Preserve aspect ratio
    plt.title(f"Traced Points from '{svg_file}'")
    plt.xlabel('X (user units)')
    plt.ylabel('Y (user units)')
    plt.legend(markerscale=4, fontsize='small', ncol=2)
    plt.tight_layout()
    plt.show()


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python trace_svg.py <your_file.svg> [samples_per_path]")
        sys.exit(1)

    
    #for k in Cutter.keys:
        
    

    svg_file = sys.argv[1]
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    size = get_svg_size(svg_file)
    print(size)
    vectors = trace_svg(svg_file, samples, width=size["width"], height=size["height"])
    
    s = Cutter("COM4", timeout=5, baudrate=198347)
    
    print(s.cmd(bytearray([0x18])))
    print(s.version())
    
    s.cmd(bytearray([0x22]), check_return=False)
    s.cmd(bytearray([0x21]), check_return=False)
    
    #s.cmd(bytearray([0x21]))
    #s.cmd40(2, 100, 100)
    #exit()
    for v in vectors:
        s.cmd40(2, int((v[0][0])), int((v[0][1])))
        print("starting shape")
        for p in v:
            print("Trace: ", int((p[0])), ", ", int((p[1])))
            s.cmd40(0, int((p[0])), int((p[1])))
            plt.scatter(int((p[0])), int((p[1])))
            time.sleep(.01)
        plast = None
        for p in v[:10]:
            print("Trace: ", int((p[0])), ", ", int((p[1])))
            s.cmd40(0, int((p[0])), int((p[1])))
            plt.scatter(int((p[0])), int((p[1])))
            time.sleep(.01)
            plast = p
        s.cmd40(6, int((plast[0])), int((plast[1])))
        
        #plt.show()
        time.sleep(1)
        
    
    #print(xxtea.encrypt(s.cmd40(2, 0, 0), bytearray(s.keys[-1])).hex())
    s.cmd(bytearray([0x22]), check_return=False)
    
    
    
    
    

    #plot_svg_points(svg_file, samples)
    #
    #
    #min_x, min_y, max_x, max_y = compute_svg_bbox(svg_file)
    #width  = max_x - min_x
    #height = max_y - min_y
    #
    #print(f"Min X: {min_x:.2f}, Min Y: {min_y:.2f}")
    #print(f"Max X: {max_x:.2f}, Max Y: {max_y:.2f}")
    #print(f"Computed Width:  {width:.2f} units")
    #print(f"Computed Height: {height:.2f} units")