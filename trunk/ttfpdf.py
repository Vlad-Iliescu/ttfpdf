# -*- coding: utf-8 -*-
# ******************************************************************************
# * Software: TFPDF for python                                                 *
# * FPDF Version:  1.7                                                         *
# * Date:     2012-08-01                                                       *
# * License:  LGPL v3.0                                                        *
# *                                                                            *
# * Original Author FPDF (PHP):  Olivier PLATHEY 2004-12-31                    *
# * Ported to Python 2.4 by Max (maxpat78@yahoo.it) on 2006-05                 *
# * Original Author tFPDF(PHP):  Ian BACK 2011-09-24                           *
# *****************************************************************************/

from datetime import datetime
import os
import zlib
import struct
import re
import uuid
import hashlib
import math

try:
    # Check if PIL is available, necessary for JPEG support.
    import Image
except ImportError:
    Image = None

def substr(s, start, length=None):
    """ Gets a substring from a string"""
    if length is None:
       length = len(s) - start
    return s[start:start+length]

def sprintf(fmt, *args):
    """Returns a formatted string"""
    return fmt % args

def mb_substr(s, start, length=None, encoding='UTF-8') :
    u_s = s.decode(encoding)
    return (u_s[start:(start+length)] if length else u_s[start:]).encode(encoding)

def mb_strlen(string, encoding='UTF-8'):
    return len(string.decode(encoding))

# Global variables
FPDF_VERSION = '0.9'
FPDF_FONT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),'font')

class TTFPDF:
#Private properties
#~
#~ page;               #current page number
#~ n;                  #current object number
#~ offsets;            #array of object offsets
#~ buffer;             #buffer holding in-memory PDF
#~ pages;              #array containing pages
#~ state;              #current document state
#~ compress;           #compression flag
#~ def_orientation;     #default orientation
#~ cur_orientation;     #current orientation
#~ orientation_changes; #array indicating orientation changes
#~ k;                  #scale factor (number of points in user unit)
#~ fw_pt,fh_pt;         #dimensions of page format in points
#~ fw,fh;             #dimensions of page format in user unit
#~ w_pt,h_pt;           #current dimensions of page in points
#~ w,h;               #current dimensions of page in user unit
#~ l_margin;            #left margin
#~ t_margin;            #top margin
#~ r_margin;            #right margin
#~ b_margin;            #page break margin
#~ c_margin;            #cell margin
#~ x,y;               #current position in user unit for cell positioning
#~ lasth;              #height of last cell printed
#~ line_width;          #line width in user unit
#~ core_fonts;          #array of standard font names
#~ fonts;              #array of used fonts
#~ font_files;          #array of font files
#~ diffs;              #array of encoding differences
#~ images;             #array of used images
#~ page_links;          #array of links in pages
#~ links;              #array of internal links
#~ font_family;         #current font family
#~ font_style;          #current font style
#~ underline;          #underlining flag
#~ current_font;        #current font info
#~ font_size_pt;         #current font size in points
#~ font_size;           #current font size in user unit
#~ draw_color;          #commands for drawing color
#~ fill_color;          #commands for filling color
#~ text_color;          #commands for text color
#~ color_flag;          #indicates whether fill and text colors are different
#~ ws;                 #word spacing
#~ auto_page_break;      #automatic page breaking
#~ page_break_trigger;   #threshold used to trigger page breaks
#~ in_footer;           #flag set when processing footer
#~ zoom_mode;           #zoom display mode
#~ layout_mode;         #layout display mode
#~ title;              #title
#~ subject;            #subject
#~ author;             #author
#~ keywords;           #keywords
#~ creator;            #creator
#~ alias_nb_pages;       #alias for total number of pages
#~ pdf_version;         #PDF version number
#~ encrypted;         #whether document is protected
#~ u_value;         #U entry in pdf document
#~ o_value;         #O entry in pdf document
#~ p_value;         #P entry in pdf document
#~ enc_obj_id;         #encryption object id
#~ last_rc4_key;         #last RC4 key encrypted (cached for optimisation)
#~ last_rc4_key_c;         #last RC4 computed key

# ******************************************************************************
# *                                                                              *
# *                               Public methods                                 *
# *                                                                              *
# *******************************************************************************/
    def __init__(self, orientation='P',unit='mm',size='A4'):
        #Some checks
        self._dochecks()
        #Initialization of properties
        self.page = 0
        self.n = 2
        self.buffer = ''
        self.pages = {}
        self.page_sizes = {}
        self.state = 0
        self.fonts = {}
        self.font_files = {}
        self.diffs = {}
        self.images = {}
        self.links = {}
        self.in_header = 0
        self.in_footer = 0
        self.lasth = 0
        self.font_family = ''
        self.font_style = ''
        self.font_size_pt = 12
        self.underline = 0
        self.draw_color = '0 G'
        self.fill_color = '0 g'
        self.text_color = '0 g'
        self.color_flag = 0
        self.ws = 0
        #Standard fonts
        self.core_fonts = {'courier', 'helvetica', 'times', 'symbol', 'zapfdingbats'}
        #Scale factor
        if unit == 'pt':
            self.k = 1
        elif unit == 'mm':
            self.k = 72/25.4
        elif unit == 'cm':
            self.k = 72/2.54
        elif unit == 'in':
            self.k = 72
        else:
            self.error('Incorrect unit: '+unit)
        #Page Sizes
        self.std_page_sizes = {
            'a3':(841.89,1190.55),
            'a4':(595.28,841.89),
            'a5':(420.94,595.28),
            'letter':(612.0,792.0),
            'legal':(612.0,1008.0)
        }
        size = self._getpagesize(size)
        self.def_page_size = self.cur_page_size = size
        #Page orientation
        orientation = orientation.lower()
        if orientation == 'p' or orientation == 'portrait':
            self.def_orientation = 'P'
            self.w = size[0]
            self.h = size[1]
        elif orientation == 'l' or orientation == 'landscape':
            self.def_orientation = 'L'
            self.w = size[1]
            self.h = size[0]
        else:
            self.error('Incorrect orientation: '+orientation)
        self.cur_orientation = self.def_orientation
        self.w_pt = self.w * self.k
        self.h_pt = self.h * self.k
        #Page margins (1 cm)
        margin = 28.35 / self.k
        self.set_margins(margin, margin)
        #Interior cell margin (1 mm)
        self.c_margin = margin / 10.0
        #line width (0.2 mm)
        self.line_width = 0.567 / self.k
        #Automatic page break
        self.set_auto_page_break(1, 2*margin)
        #Full width display mode
        self.set_display_mode('default')
        #Enable compression
        self.set_compression(True)
        #Set default PDF version number
        self.pdf_version = '1.3'
        self.unifont_subset = None
        self.offsets = {}
        self.page_links = []

        self.encrypted = False
        self.last_rc4_key = ''
        self.padding = "\x28\xBF\x4E\x5E\x4E\x75\x8A\x41\x64\x00\x4E\x56\xFF\xFA\x01\x08"\
            "\x2E\x2E\x00\xB6\xD0\x68\x3E\x80\x2F\x0C\xA9\xFE\x64\x53\x69\x7A"

        self.files = []
        self.n_files = 0

        self.gradients = []

    def set_margins(self, left, top, right=None):
        """Set left, top and right margins"""
        self.l_margin = left
        self.t_margin = top
        if right is None:
            right = left
        self.r_margin = right

    def set_left_margin(self, margin):
        """Set left margin"""
        self.l_margin = margin
        if self.page > 0 and self.x < margin:
            self.x = margin

    def set_top_margin(self, margin):
        """Set top margin"""
        self.t_margin = margin

    def set_right_margin(self, margin):
        """Set right margin"""
        self.r_margin = margin

    def set_auto_page_break(self, auto, margin=0):
        """Set auto page break mode and triggering margin"""
        self.auto_page_break = auto
        self.b_margin = margin
        self.page_break_trigger = self.h - margin

    def set_display_mode(self, zoom, layout = 'default'):
        """Set display mode in viewer"""
        if zoom == 'fullpage' or zoom == 'fullwidth' or zoom == 'real' \
           or zoom=='default' or not isinstance(zoom, basestring):
            self.zoom_mode = zoom
        else:
            self.error('Incorrect zoom display mode: '+zoom)
        if layout == 'single' or layout == 'continuous' or layout == 'two' \
            or layout == 'default':
            self.layout_mode = layout
        else:
            self.error('Incorrect layout display mode: '+layout)

    def set_compression(self, compress):
        """Set page compression"""
        self.compress = compress

    def set_title(self, title, is_UTF8=False):
        """Title of document"""
        if is_UTF8:
            title = self.UTF8_to_UTF16BE(title)
        self.title = title

    def set_subject(self, subject, is_UTF8=False):
        """Subject of document"""
        if is_UTF8:
            subject = self.UTF8_to_UTF16BE(subject)
        self.subject = subject

    def set_author(self, author, is_UTF8=False):
        """Author of document"""
        if is_UTF8:
            author = self.UTF8_to_UTF16BE(author)
        self.author = author

    def set_keywords(self, keywords, is_UTF8=False):
        """Keywords of document"""
        if is_UTF8:
            keywords = self.UTF8_to_UTF16BE(keywords)
        self.keywords = keywords

    def set_creator(self, creator, is_UTF8=False):
        """Creator of document"""
        if is_UTF8:
            creator = self.UTF8_to_UTF16BE(creator)
        self.creator = creator

    def alias_nb_pages(self, alias='{nb}'):
        """Define an alias for total number of pages"""
        self.str_alias_nb_pages = alias

    def error(self, msg):
        """Fatal error"""
        raise RuntimeError('FPDF error: '+msg)

    def open(self):
        """Begin document"""
        self.state = 1

    def close(self):
        """Terminate document"""
        if self.state == 3:
            return
        if self.page == 0:
            self.add_page()
        #Page footer
        self.in_footer = 1
        self.footer()
        self.in_footer = 0
        #close page
        self._endpage()
        #close document
        self._enddoc()

    def add_page(self, orientation='', size = ''):
        """Start a new page"""
        if self.state == 0:
            self.open()
        family = self.font_family
        if self.underline:
            style = self.font_style + 'U'
        else:
            style = self.font_style
        font_size = self.font_size_pt
        lw = self.line_width
        dc = self.draw_color
        fc = self.fill_color
        tc = self.text_color
        cf = self.color_flag
        if self.page > 0:
            #Page footer
            self.in_footer = 1
            self.footer()
            self.in_footer = 0
            #close page
            self._endpage()
        #Start new page
        self._beginpage(orientation, size)
        #Set line cap style to square
        self._out('2 J')
        #Set line width
        self.line_width = lw
        self._out(sprintf('%.2f w', lw*self.k))
        #Set font
        if family:
            self.set_font(family, style, font_size)
        #Set colors
        self.draw_color = dc
        if dc != '0 G':
            self._out(dc)
        self.fill_color = fc
        if fc != '0 g':
            self._out(fc)
        self.text_color = tc
        self.color_flag = cf
        #Page header
        self.in_header = 1
        self.header()
        self.in_header = 0
        #Restore line width
        if self.line_width != lw:
            self.line_width = lw
            self._out(sprintf('%.2f w', lw*self.k))
        #Restore font
        if family:
            self.set_font(family, style, font_size)
        #Restore colors
        if self.draw_color != dc:
            self.draw_color = dc
            self._out(dc)
        if self.fill_color != fc:
            self.fill_color = fc
            self._out(fc)
        self.text_color = tc
        self.color_flag = cf

    def header(self):
        """Header to be implemented in your own inherited class"""
        pass

    def footer(self):
        """Footer to be implemented in your own inherited class"""
        pass

    def page_no(self):
        """Get current page number"""
        return self.page

    def set_draw_color(self, r, g=None, b=None):
        """Set color for all stroking operations"""
        if(r == 0 and g == 0 and b == 0) or g is None:
            self.draw_color = sprintf('%.3f G', r/255.0)
        else:
            self.draw_color = sprintf('%.3f %.3f %.3f RG', r/255.0, g/255.0, b/255.0)
        if self.page > 0:
            self._out(self.draw_color)

    def set_fill_color(self, r, g=None, b=None):
        """Set color for all filling operations"""
        if(r == 0 and g == 0 and b == 0) or g is None:
            self.fill_color = sprintf('%.3f g', r/255.0)
        else:
            self.fill_color = sprintf('%.3f %.3f %.3f rg',r/255.0,g/255.0,b/255.0)
        self.color_flag = (self.fill_color != self.text_color)
        if self.page > 0:
            self._out(self.fill_color)

    def set_text_color(self, r, g=None, b=None):
        """Set color for text"""
        if (r == 0 and g == 0 and b == 0) or g is None:
            self.text_color = sprintf('%.3f g', r/255.0)
        else:
            self.text_color = sprintf('%.3f %.3f %.3f rg', r/255.0, g/255.0, b/255.0)
        self.color_flag = (self.fill_color != self.text_color)

    def get_string_width(self, s):
        """Get width of a string in the current font"""
        cw = self.current_font['cw']
        w = 0
        if self.unifont_subset:
            unicode_str = self.UTF8_string_to_array(s)
            for char in unicode_str:
                if char < len(cw):
                    w += (ord(cw[2*char])<<8) + ord(cw[2*char+1])
                elif 0 < char < 128 and chr(char) in cw:
                    w += cw[chr(char)]
                elif 'desc' in self.current_font and 'MissingWidth' in self.current_font['desc']:
                    w += self.current_font['desc']['MissingWidth']
                elif 'MissingWidth' in self.current_font:
                    w += self.current_font['MissingWidth']
                else:
                    w += 500
        else:
            l = len(s)
            for i in xrange(l):
                w += cw.get(s[i],0)
        return w * self.font_size / 1000.0

    def set_line_width(self, width):
        """Set line width"""
        self.line_width = width
        if self.page > 0:
            self._out(sprintf('%.2f w', width*self.k))

    def line(self, x1, y1, x2, y2):
        """Draw a line"""
        self._out(sprintf('%.2f %.2f m %.2f %.2f l S', x1*self.k, (self.h-y1)*self.k, x2*self.k, (self.h-y2)*self.k))

    def rect(self, x, y, w, h, style=''):
        """Draw a rectangle"""
        if style == 'F':
            op = 'f'
        elif style == 'FD' or style == 'DF':
            op = 'B'
        else:
            op = 'S'
        self._out(sprintf('%.2f %.2f %.2f %.2f re %s', x*self.k, (self.h-y)*self.k, w*self.k, -h*self.k, op))

    def add_font(self, family, style='', file='', uni=False):
        """AAdd a TrueType, OpenType or Type1 font"""
        family = family.lower()
        style = style.upper()
        if style == 'IB':
            style = 'BI'
        if file == '':
            if uni:
                file = family.replace(' ','') + style.lower() + '.ttf'
            else:
                file = family.replace(' ','') + style.lower() + '.py'
        if family == 'arial':
            family = 'helvetica'
        fontkey = family + style
        if fontkey in self.fonts:
            self.error('Font already added: '+family+' '+style)
        if uni:
            ttf_filename = os.path.join(self._getfontpath(), 'unitfont', file)
            unifilename = os.path.join(self._getfontpath(), 'unitfont', file.split('.')[0].lower())
            name = ''
            originalsize = 0
            ttf_stat = os.stat(ttf_filename)
            if os.path.exists(unifilename+'.mtx.py'):
                fontimport = {}
                execfile(unifilename+'.mtx.py',globals(),fontimport)
                type = fontimport.get('type')
                name = fontimport.get('name')
                originalsize = fontimport.get('originalsize')
                desc = fontimport.get('desc')
                up = fontimport.get('up')
                ut = fontimport.get('ut')
                ttffile = fontimport.get('ttffile')
                fontkey = fontimport.get('fontkey')
            try:
                isset = not ( type is None or name is None or originalsize is None or desc is None
                              or up is None or ut is None or ttffile is None or fontkey is None)
            except Exception as e:
                isset = False
            if not isset:
                ttffile = ttf_filename
                from font.unitfont import TTFontFile
                ttf = TTFontFile()
                ttf.get_metrics(ttffile)
                cw = ttf.char_widths
                name = re.sub('[ ()]', '', ttf.full_name)
                desc = {
                    'Ascent': int(ttf.ascent),
                    'Descent': int(ttf.descent),
                    'CapHeight': int(ttf.cap_height),
                    'Flags': int(ttf.flags),
                    'FontBBox': '[{0} {1} {2} {3}]'.format(*[str(int(b)) for b in ttf.bbox]),
                    'ItalicAngle': int(ttf.italic_angle),
                    'StemV' : int(ttf.stem_v),
                    'MissingWidth': int(ttf.default_width)
                }
                up = int(ttf.underline_position)
                ut = int(ttf.underline_thickness)
                originalsize = ttf_stat.st_size
                type = 'TTF'
                #Generate metrics .py file

                s = "\n".join([
                    'name = "{0}"'.format(name),
                    'type = "{0}"'.format(type),
                    'desc = {0}'.format(desc),
                    'up = {0}'.format(up),
                    'ut = {0}'.format(ut),
                    'ttffile = "{0}"'.format(ttffile.replace('\\','\\\\')),
                    'originalsize = {0}'.format(originalsize),
                    'fontkey = "{0}"'.format(fontkey)
                ])

                if os.access(os.path.join(self._getfontpath(), 'unitfont'), os.W_OK):
                    fh = open(unifilename+'.mtx.py','w')
                    fh.write(s)
                    fh.close()
                    fh = open(unifilename+'.cw.dat', 'wb')
                    fh.write(cw)
                    fh.close()
                    #os.unlink(unifilename + '.cw127.py')
                del ttf
            else:
                cw = open(unifilename+'.cw.dat', 'rb').read()
            i = len(self.fonts) + 1
            if hasattr(self, 'str_alias_nb_pages'):
                sbarr = {}
                for x in xrange(0, 57):
                    sbarr[x] = x
            else:
                sbarr = {}
                for x in xrange(0, 32):
                    sbarr[x] = x
            self.fonts[fontkey] = dict(i = i, type = type, name = name, desc = desc, up = up, ut = ut, cw = cw ,
                ttffile = ttffile, fontkey = fontkey, subset = sbarr, unifilename = unifilename)

            self.font_files[fontkey] = {'length1':originalsize, 'type':'TTF', 'ttffile':ttffile}
            self.font_files[file] = {'type': 'TTF'}
            del cw
        else:
            info = self._loadfont(file)
            info['i'] = len(self.fonts) + 1
            if info.get('diff'):
                #Search existing encodings
                n = info['diff'] in self.diffs
                if not n:
                    n = len(self.diffs) + 1
                    self.diffs[n] = info['diff']
                info['diffn'] = n
            if info.get('file'):
                #Embedded font
                if info['type'] == 'TrueType':
                    self.font_files[info['file']] = {'length1': info['originalsize']}
                else:
                    self.font_files[info['file']] = {'length1': info['size1'], 'length2': info['size2']}
            self.fonts[fontkey] = info

    def set_font(self, family, style='', size=0):
        """Select a font; size given in points"""
        family = family.lower()
        if family == '':
            family = self.font_family
        if family == 'arial':
            family = 'helvetica'
        elif family == 'symbol' or family == 'zapfdingbats':
            style=''
        style = style.upper()
        if 'U' in style:
            self.underline = 1
            style = style.replace('U', '')
        else:
            self.underline = 0
        if style == 'IB':
            style = 'BI'
        if size == 0:
            size = self.font_size_pt
        #Test if font is already selected
        if self.font_family == family and self.font_style == style and self.font_size_pt == size:
            return
        #Test if used for the first time
        fontkey = family+style
        #Test if font is already loaded
        if fontkey not in self.fonts:
            #Check if one of the standard fonts
            if fontkey in self.core_fonts:
                self.add_font(family, style)
            else:
                self.error('Undefined font: {0} {1}'.format(family, style))
        #Select it
        self.font_family = family
        self.font_style = style
        self.font_size_pt = size
        self.font_size = size / self.k
        self.current_font = self.fonts[fontkey]
        if self.fonts[fontkey]['type'] == 'TTF':
            self.unifont_subset = True
        else:
            self.unifont_subset = False
        if self.page > 0:
            self._out(sprintf('BT /F%d %.2f Tf ET', self.current_font['i'], self.font_size_pt))

    def set_font_size(self, size):
        """Set font size in points"""
        if self.font_size_pt == size:
            return
        self.font_size_pt = size
        self.font_size = size / self.k
        if self.page > 0:
            self._out(sprintf('BT /F%d %.2f Tf ET', self.current_font['i'], self.font_size_pt))

    def add_link(self):
        """Create a new internal link"""
        n = len(self.links) + 1
        self.links[n] = (0,0)
        return n

    def set_link(self, link, y=0, page=None):
        """Set destination of internal link"""
        if y == -1:
            y = self.y
        if page is None:
            page = self.page
        self.links[link] = [page,y]

    def link(self, x, y, w, h, link):
        """Put a link on the page"""
        if not self.page in self.page_links:
            self.page_links[self.page] = []
        self.page_links[self.page].append((x*self.k, self.h_pt-y*self.k, w*self.k, h*self.k, link))

    def text(self, x, y, txt):
        """Output a string"""
        if self.unifont_subset:
            txt2 = self._escape(self.UTF8_to_UTF16BE(txt, False))
            for uni in self.UTF8_string_to_array(txt):
                self.current_font['subset'][uni] = uni
        else:
            txt2 = self._escape(txt)
        s = sprintf('BT %.2f %.2f Td (%s) Tj ET', x*self.k, (self.h-y)*self.k, txt2)
        if self.underline and txt != '':
            s += ' ' + self._dounderline(x, y, txt)
        if self.color_flag:
            s = 'q ' + self.text_color + ' '+ s + ' Q'
        self._out(s)

    def text_with_direction(self, x, y, txt, direction = 'R'):
        if self.unifont_subset:
            txt2 = self._escape(self.UTF8_to_UTF16BE(txt, False))
            for uni in self.UTF8_string_to_array(txt):
                self.current_font['subset'][uni] = uni
        else:
            txt2 = self._escape(txt)

        if direction == 'R':
            s = sprintf('BT %.2f %.2f %.2f %.2f %.2f %.2f Tm (%s) Tj ET', 1, 0, 0, 1, x*self.k, (self.h-y)*self.k, txt2)
        elif direction == 'L':
            s = sprintf('BT %.2f %.2f %.2f %.2f %.2f %.2f Tm (%s) Tj ET', -1, 0, 0, -1, x*self.k, (self.h-y)*self.k, txt2)
        elif direction == 'U':
            s = sprintf('BT %.2f %.2f %.2f %.2f %.2f %.2f Tm (%s) Tj ET', 0, 1, -1, 0, x*self.k, (self.h-y)*self.k, txt2)
        elif direction == 'D':
            s = sprintf('BT %.2f %.2f %.2f %.2f %.2f %.2f Tm (%s) Tj ET', 0, -1, 1, 0, x*self.k, (self.h-y)*self.k, txt2)
        else:
            s = sprintf('BT %.2f %.2f Td (%s) Tj ET', x*self.k, (self.h-y)*self.k, txt2)
#        if self.underline and txt != '':
#            s += ' ' + self._dounderline(x, y, txt)
        if self.color_flag:
            s = 'q ' + self.text_color + ' '+ s + ' Q'
        self._out(s)

    def text_with_rotation(self, x, y, txt, txt_angle, font_angle=0):
        if self.unifont_subset:
            txt2 = self._escape(self.UTF8_to_UTF16BE(txt, False))
            for uni in self.UTF8_string_to_array(txt):
                self.current_font['subset'][uni] = uni
        else:
            txt2 = self._escape(txt)

        font_angle += 90 + txt_angle
        txt_angle *= math.pi / 180.0
        font_angle *= math.pi / 180.0

        txt_dx = math.cos(txt_angle)
        txt_dy = math.sin(txt_angle)
        font_dx = math.cos(font_angle)
        font_dy = math.sin(font_angle)

        s = sprintf('BT %.2f %.2f %.2f %.2f %.2f %.2f Tm (%s) Tj ET', txt_dx, txt_dy, font_dx, font_dy, x*self.k,
                    (self.h-y)*self.k, txt2)
        if self.color_flag:
            s = 'q ' + self.text_color + ' '+ s + ' Q'
        self._out(s)

    def accept_page_break(self):
        """Accept automatic page break or not"""
        return self.auto_page_break

    def cell(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=''):
        """Output a cell"""
        k = self.k
        if self.y + h > self.page_break_trigger and not self.in_header \
           and not self.in_footer and self.accept_page_break():
            #Automatic page break
            x = self.x
            ws = self.ws
            if ws > 0:
                self.ws = 0
                self._out('0 Tw')
            self.add_page(self.cur_orientation, self.cur_page_size)
            self.x = x
            if ws > 0:
                self.ws = ws
                self._out(sprintf('%.3f Tw', ws*k))
        if w == 0:
            w = self.w - self.r_margin - self.x
        s = ''
        if fill or border == 1:
            if fill:
                if border == 1:
                    op = 'B'
                else:
                    op = 'f'
            else:
                op = 'S'
            s = sprintf('%.2f %.2f %.2f %.2f re %s ', self.x*k, (self.h - self.y)*k, w*k, -h*k, op)
        if isinstance(border, basestring):
            x = self.x
            y = self.y
            if 'L' in border:
                s += sprintf('%.2f %.2f m %.2f %.2f l S ', x*k, (self.h-y)*k, x*k, (self.h-(y+h))*k)
            if 'T' in border:
                s += sprintf('%.2f %.2f m %.2f %.2f l S ', x*k, (self.h-y)*k, (x+w)*k, (self.h-y)*k)
            if 'R' in border:
                s += sprintf('%.2f %.2f m %.2f %.2f l S ', (x+w)*k, (self.h-y)*k, (x+w)*k, (self.h-(y+h))*k)
            if 'B' in border:
                s += sprintf('%.2f %.2f m %.2f %.2f l S ', x*k, (self.h-(y+h))*k, (x+w)*k, (self.h-(y+h))*k)
        if txt != '':
            if align == 'R':
                dx = w - self.c_margin - self.get_string_width(txt)
            elif align == 'C':
                dx = (w - self.get_string_width(txt)) / 2.0
            else:
                dx = self.c_margin
            if self.color_flag:
                s += 'q ' + self.text_color + ' '

            #If multibyte, Tw has no effect - do word spacing using an adjustment before each space
            if self.ws and self.unifont_subset:
                for uni in self.UTF8_string_to_array(txt):
                    self.current_font['subset'][uni] = uni
                space = self._escape(self.UTF8_to_UTF16BE(' ', False))
                s += sprintf('BT 0 Tw %.2f %.2f Td [', (self.x + dx)*k,
                                (self.h - (self.y + 0.5 * h + 0.3 * self.font_size))*k)
                t = txt.split(' ')
                for i in xrange(len(t)):
                    tx = t[i]
                    tx = self._escape(self.UTF8_to_UTF16BE(tx, False))
                    s += sprintf('(%s)', tx)
                    if i+1 < len(t):
                        adj = -(self.ws * self.k) * 1000 / self.font_size
                        s += sprintf('%d(%s) ', adj, space)
                s += '] TJ ET'
            else:
                if self.unifont_subset:
                    txt2 = self._escape(self.UTF8_to_UTF16BE(txt, False))
                    for uni in self.UTF8_string_to_array(txt):
                        self.current_font['subset'][uni] = uni
                else:
                    txt2 = txt.replace('\\','\\\\').replace(')','\\)').replace('(','\\(')
                s += sprintf('BT %.2f %.2f Td (%s) Tj ET',(self.x+dx)*k,
                             (self.h-(self.y+.5*h+.3*self.font_size))*k, txt2)
            if self.underline:
                s+= ' ' + self._dounderline(self.x+dx, self.y+.5*h+.3*self.font_size, txt)
            if self.color_flag:
                s+=' Q'
            if link:
                self.link(self.x+dx, self.y+.5*h-.5*self.font_size, self.get_string_width(txt), self.font_size,link)
        if s:
            self._out(s)
        self.lasth = h
        if ln > 0:
            #Go to next line
            self.y += h
            if ln==1:
                self.x = self.l_margin
        else:
            self.x += w

    def multi_cell(self, w, h, txt, border=0, align='J', fill=0, split_only=False):
        """Output text with automatic or explicit line breaks"""
        ret = [] # if split_only = True, returns splited text cells
        cw = self.current_font['cw']
        if w == 0:
            w = self.w - self.r_margin - self.x
        wmax = (w - 2 * self.c_margin)
        s = txt.replace("\r",'')
        if self.unifont_subset:
            nb = mb_strlen(s, 'UTF-8')
            while nb > 0 and mb_substr(s, nb-1, 1, 'UTF-8') == "\n":
                nb -= 1
        else:
            nb = len(s)
            if nb > 0 and s[nb-1] == "\n":
                nb -= 1
        b = 0
        if border:
            if border == 1:
                border='LTRB'
                b='LRT'
                b2='LR'
            else:
                b2=''
                if 'L' in border:
                    b2 += 'L'
                if 'R' in border:
                    b2 += 'R'
                if 'T' in border:
                    b= b2 + 'T'
                else:
                    b = b2
        sep = -1
        i = 0
        j = 0
        l = 0
        ns = 0
        nl = 1
        while i < nb:
            #Get next character
            if self.unifont_subset:
                c = mb_substr(s, i, 1, 'UTF-8')
            else:
                c = s[i]
            if c == "\n":
                #Explicit line break
                if self.ws > 0:
                    self.ws = 0
                    self._out('0 Tw')
                if self.unifont_subset:
                    if not split_only:
                        self.cell(w, h, mb_substr(s, j, i-j, 'UTF-8'), b, 2, align, fill)
                    else:
                        ret.append(mb_substr(s, j, i-j, 'UTF-8'))
                else:
                    if not split_only:
                        self.cell(w, h, substr(s, j, i-j), b, 2, align, fill)
                    else:
                        ret.append(substr(s, j, i-j))
                i += 1
                sep = -1
                j = i
                l = 0
                ns = 0
                nl += 1
                if border and nl == 2:
                    b = b2
                continue
            if c == ' ':
                sep = i
                ls = l
                ns += 1
            if self.unifont_subset:
                l += self.get_string_width(c)
            else:
                l += cw.get(c,0) * self.font_size / 1000.0
            if l > wmax:
                #Automatic line break
                if sep == -1:
                    if i == j:
                        i += 1
                    if self.ws > 0:
                        self.ws = 0
                        self._out('0 Tw')
                    if self.unifont_subset:
                        if not split_only:
                            self.cell(w, h, mb_substr(s, j, i-j, 'UTF-8'), b, 2, align, fill)
                        else:
                            ret.append(mb_substr(s, j, i-j, 'UTF-8'))
                    else:
                        if not split_only:
                            self.cell(w, h, substr(s, j, i-j), b, 2, align, fill)
                        else:
                            ret.append(substr(s, j, i-j))
                else:
                    if align == 'J':
                        if ns > 1:
                            self.ws = (wmax - ls) / (ns - 1)
                        else:
                            self.ws = 0
                        self._out(sprintf('%.3f Tw', self.ws * self.k))
                    if self.unifont_subset:
                        if not split_only:
                            self.cell(w, h, mb_substr(s, j, sep-j,'UTF-8'), b, 2, align, fill)
                        else:
                            ret.append(mb_substr(s, j, sep-j,'UTF-8'))
                    else:
                        if not split_only:
                            self.cell(w, h, substr(s, j, sep-j), b, 2, align, fill)
                        else:
                            ret.append(substr(s, j, sep-j))
                    i = sep + 1
                sep = -1
                j = i
                l = 0
                ns = 0
                nl += 1
                if border and nl == 2:
                    b = b2
            else:
                i += 1
        #Last chunk
        if self.ws > 0:
            self.ws = 0
            self._out('0 Tw')

        if border and 'B' in border:
            b += 'B'
        if self.unifont_subset:
            if not split_only:
                self.cell(w, h, mb_substr(s, j, i-j, 'UTF-8'), b, 2, align, fill)
            else:
                ret.append(mb_substr(s, j, i-j, 'UTF-8'))
        else:
            if not split_only:
                self.cell(w, h, substr(s, j, i-j), b, 2, align, fill)
            else:
                ret.append(substr(s, j, i-j))
        self.x = self.l_margin
        return ret

    def cell_fit_scale(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=''):
        """Cell with horizontal scaling only if necessary"""
        self._cell_fit(w, h, txt, border, ln, align, fill, link, True, False)

    def cell_fit_scale_force(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=''):
        """Cell with horizontal scaling always"""
        self._cell_fit(w, h, txt, border, ln, align, fill, link, True, True)

    def cell_fit_space(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=''):
        """Cell with character spacing only if necessary"""
        self._cell_fit(w, h, txt, border, ln, align, fill, link, False, False)

    def cell_fit_space_force(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=''):
        """Cell with character spacing always"""
        self._cell_fit( w, h, txt, border, ln, align, fill, link, False, True)

    def write(self, h, txt, link=''):
        """Output text in flowing mode"""
        cw = self.current_font['cw']
        w = self.w - self.r_margin - self.x
        wmax = (w - 2 * self.c_margin)
        s = txt.replace("\r",'')
        if self.unifont_subset:
            nb = mb_strlen(s, 'UTF-8')
            if nb == 1 and s == ' ':
                self.x += self.get_string_width(s)
                return
        else:
            nb = len(s)

        sep = -1
        i = 0
        j = 0
        l = 0
        nl = 1
        while i < nb:
            #Get next character
            if self.unifont_subset:
                c = mb_substr(s, i, 1)
            else:
                c = s[i]
            if c == "\n":
                #Explicit line break
                if self.unifont_subset:
                    self.cell(w, h, mb_substr(s, j, i - j), 0, 2, '', 0, link)
                else:
                    self.cell(w, h, substr(s, j, i-j), 0, 2, '', 0, link)
                i += 1
                sep = -1
                j = i
                l = 0
                if nl == 1:
                    self.x = self.l_margin
                    w = self.w - self.r_margin - self.x
                    wmax = (w - 2 * self.c_margin)
                nl += 1
                continue
            if c == ' ':
                sep = i
            if self.unifont_subset:
                l += self.get_string_width(c)
            else:
                l += cw.get(c,0) * self.font_size / 1000.0
            if l > wmax:
                #Automatic line break
                if sep == -1:
                    if self.x > self.l_margin:
                        #Move to next line
                        self.x = self.l_margin
                        self.y += h
                        w = self.w - self.r_margin - self.x
                        wmax = (w - 2 * self.c_margin)
                        i += 1
                        nl += 1
                        continue
                    if i == j:
                        i += 1
                    if self.unifont_subset:
                        self.cell(w, h, mb_substr(s, j, i-j,'UTF-8'), 0, 2, '', 0, link)
                    else:
                        self.cell(w,h,substr(s,j,i-j),0,2,'',0,link)
                else:
                    if self.unifont_subset:
                        self.cell(w, h, mb_substr(s, j, sep-j,'UTF-8'), 0, 2, '', 0, link)
                    else:
                        self.cell(w, h, substr(s, j, sep-j), 0, 2, '', 0, link)
                    i = sep + 1
                sep = -1
                j = i
                l = 0
                if nl == 1:
                    self.x = self.l_margin
                    w = self.w - self.r_margin - self.x
                    wmax = (w - 2 * self.c_margin)
                nl += 1
            else:
                i += 1
        #Last chunk
        if i != j:
            if self.unifont_subset:
                self.cell(l, h, mb_substr(s, j, i- j,'UTF-8'), 0, 0, '', 0, link)
            else:
                self.cell(l, h, substr(s,j), 0, 0, '', 0, link)

    def ln(self, h=''):
        """Line Feed; default value is last cell height"""
        self.x = self.l_margin
        if isinstance(h, basestring):
            self.y += self.lasth
        else:
            self.y += h

    def image(self, file, x = None, y = None, w=0, h=0, type='', link=''):
        """Put an image on the page"""
        if not file in self.images:
            #First use of image, get info
            if type == '':
                pos = file.rfind('.')
                if not pos:
                    self.error('Image file has no extension and no type was specified: '+file)
                type = substr(file, pos + 1)
            type = type.lower()
            if type == 'jpg' or type == 'jpeg':
                info = self._parsejpg(file)
            elif type == 'png':
                info = self._parsepng(file)
            else:   #TODO GIF SUPPORT
                #Allow for additional formats
                mtd = '_parse' + type
                if not (hasattr(self,mtd) and callable(getattr(self, mtd))):
                    self.error('Unsupported image type: '+type)
                info = self.mtd(file)
            info['i'] = len(self.images) + 1
            self.images[file] = info
        else:
            info = self.images[file]
        #Automatic width and height calculation if needed
        if w == 0 and h == 0:
            #Put image at 72 dpi
            w = info['w'] / self.k
            h = info['h'] / self.k
        if w == 0:
            w = h * info['w'] / info['h']
        if h == 0:
            h = w * info['h'] / info['w']

        # Flowing mode
        if y is None:
            if self.y + h  > self.page_break_trigger and not self.in_header and not self.in_footer and \
                self.accept_page_break():
                #Automatic page break
                x2 = self.x
                self.add_page(self.cur_orientation, self.cur_page_size)
                self.x = x2
            y = self.y
            self.y += h

        if x is None:
            x = self.x

        self._out(sprintf('q %.2f 0 0 %.2f %.2f %.2f cm /I%d Do Q', w * self.k, h * self.k, x * self.k,
            (self.h-(y+h)) * self.k, info['i']))
        if link:
            self.link(x, y, w, h, link)

    def get_x(self):
        """Get x position"""
        return self.x

    def set_x(self, x):
        """Set x position"""
        if x >= 0:
            self.x = x
        else:
            self.x = self.w + x

    def get_y(self):
        """Get y position"""
        return self.y

    def set_y(self, y):
        """Set y position and reset x"""
        self.x = self.l_margin
        if y >= 0:
            self.y = y
        else:
            self.y = self.h + y

    def set_xy(self, x,y):
        """Set x and y positions"""
        self.set_y(y)
        self.set_x(x)

    def output(self, name='', dest=''):
        """Output PDF to some destination"""
        #Finish document if necessary
        if self.state < 3:
            self.close()
        #Normalize parameters
        dest = dest.upper()
        if dest == '':
            if name == '':
                name = 'doc.pdf'
                dest = 'I'
            else:
                dest = 'F'
        if dest == 'I':
            #Send to standard output
            print self.buffer
        elif dest == 'D':
            #Download file
            print self.buffer
        elif dest=='F':
            #Save to local file
            f = file(name,'wb')
            if not f:
                self.error('Unable to create output file: '+name)
            f.write(self.buffer)
            f.close()
        elif dest == 'S':
            #Return as a string
            return self.buffer
        else:
            self.error('Incorrect output destination: '+dest)
        return ''

    def UTF8_string_to_array(self, s):
        """Converst an UTF-8 string to ord() list"""
        out = []
        add = out.append
        l = len(s)
        i = 0
        while i < l:
            uni = -1
            h = ord(s[i])
            if h <= 0x7F:
                uni = h
            elif h >= 0xC2:
                if h <= 0xDF and i < l-1:
                    i += 1
                    uni = (h & 0x1F) << 6 | (ord(s[i]) & 0x3F)
                elif h <= 0xEF and i < l-2:
                    uni  = (h & 0x0F) << 12 | (ord(s[i+1]) & 0x3F) << 6 | (ord(s[i+2]) & 0x3F)
                    i += 2
                elif h <= 0xF4 and i < l-3:
                    uni = (h & 0x0F) << 18 | (ord(s[i+1]) & 0x3F) << 12 | (ord(s[i+2]) & 0x3F) << 6 | (ord(s[i+3]) & 0x3F)
            if uni >= 0:
                add(uni)
            i += 1
        return out

    def UTF8_to_UTF16BE(self,s, setbom = True):
        """Convert UTF-8 to UTF-16BE with BOM"""
        if setbom:
            res = '\xFE\xFF'
        else:
            res = ''

        return res + s.decode('UTF-8').encode('UTF-16BE')

    def set_protection(self, permisions=(), user_pass='', owner_pass=None):
        options = {'print':4, 'modify':8, 'copy':16, 'annot-forms':32}
        protection = 192
        for permision in permisions:
            if permision not in options:
                self.error('Incorrect permission: '+permision)
            protection += options[permision]
        if owner_pass is None:
            owner_pass = uuid.uuid1()
        self.encrypted = True
        self._generateencryptionkey(user_pass, owner_pass, protection)

    def rounded_rectangle(self, x, y, w, h, radius, style='', corners='1234'):
        k = self.k
        hp = self.h
        if style == 'F':
            op = 'f'
        elif style == 'FD' or style == 'DF':
            op = 'B'
        else:
            op = 'S'

        arc = 4.0 / 3.0 * (2.0**0.5 - 1)
        self._out(sprintf('%.2f %.2f m', (x+radius)*k, (hp-y)*k))

        # ARC 2
        xc = x + w - radius
        yc = y + radius
        self._out(sprintf('%.2f %.2f l', xc*k, (hp-y)*k))
        if '2' in corners:
            self._arc(xc+radius*arc, yc-radius, xc+radius, yc-radius*arc, xc+radius, yc)
        else:
            self._out(sprintf('%.2f %.2f l', (x+w)*k, (hp-y)*k))

        #ARC 3
        xc = x + w - radius
        yc = y + h - radius
        self._out(sprintf('%.2f %.2f l', (x+w)*k, (hp-yc)*k))
        if '3' in corners:
            self._arc(xc+radius, yc+radius*arc, xc+radius*arc, yc+radius,  xc, yc+radius)
        else:
            self._out(sprintf('%.2f %.2f l', (x+w)*k, (hp-(y+h))*k))

        #ARC 4
        xc = x + radius
        yc= y + h - radius
        self._out(sprintf('%.2f %.2f l', xc*k, (hp-(y+h))*k))
        if '4' in corners:
            self._arc(xc-radius*arc, yc+radius, xc-radius, yc+radius*arc, xc-radius, yc)
        else:
            self._out(sprintf('%.2f %.2f l', x*k, (hp-(y+h))*k))

        #ARC 1
        xc = x + radius
        yc = y + radius
        self._out(sprintf('%.2f %.2f l', x*k, (hp-yc)*k ))
        if '1' in corners:
            self._arc(xc-radius, yc-radius*arc, xc-radius*arc, yc-radius, xc, yc-radius)
        else:
            self._out(sprintf('%.2f %.2f l', x*k, (hp-y)*k))
            self._out(sprintf('%.2f %.2f l', (x+radius)*k, (hp-y)*k))
        self._out(op)

    def shadow_cell(self, w, h=0, txt='', border=0, ln=0, align='', fill=False, link=0, color='G', distance=0.5):
        if color == 'G':
            shadow_color = 100
        elif color == 'B':
            shadow_color = 0
        else:
            shadow_color = color
        text_color = self.text_color
        x = self.x
        self.set_text_color(shadow_color)
        self.cell(w, h, txt, border, 0, align, fill, link)
        self.text_color = text_color
        self.x = x
        self.y += distance
        self.cell(w, h, txt, 0, ln, align)

    def attach(self, file, name='', desc=''):
        #also supports StringIO or any object with a .read() method
        # name is mandatory for those files
        if name == '':
            name = os.path.basename(file)
        if isinstance(file, basestring):
            file = open(file, 'rb')
        if not file:
            self.error('Cannot open file: '+name)
        self.files.append({'file': file, 'name': name, 'desc': desc})

    def start_transform(self):
        """save the current graphic state"""
        self._out('q')

    def stop_transform(self):
        """restore previous graphic state"""
        self._out('Q')

    def scale(self, s_x, s_y, x=None, y=None):
        if not x:
            x = self.x
        if not y:
            y = self.y
        if s_x == 0 or s_y == 0:
            self.error('Please use values unequal to zero for Scaling')
        y = (self.h - y) * self.k
        x *= self.k
        #calculate elements of transformation matrix
        s_x /= 100.0
        s_y /= 100.0
        tm = [s_x, 0, 0, s_y, x*(1-s_x), y*(1-s_y)]
        #scale the coordinate system
        self._transform(tm)

    def scale_xy(self, s, x=None, y=None):
        self.scale(s, s, x, y)

    def scale_x(self, s_x, x=None, y=None):
        self.scale(s_x, 100, x, y)

    def scale_y(self, s_y, x=None, y=None):
        self.scale(100, s_y, x, y)

    def translate_x(self, t_x):
        self.translate(t_x, 0)

    def translate_y(self, t_y):
        self.translate(0, t_y)

    def translate(self, t_x, t_y):
        #calculate elements of transformation matrix
        tm = [1, 0, 0, 1, t_x*self.k, t_y*self.k]
        #translate the coordinate system
        self._transform(tm)

    def rotate(self, angle, x=None, y=None):
        if not x:
            x = self.x
        if not y:
            y = self.y
        y = (self.h - y) * self.k
        x *= self.k
        #calculate elements of transformation matrix
        tm = [math.cos(math.radians(angle)), math.sin(math.radians(angle))]
        tm.append(-tm[1])
        tm.append(tm[0])
        tm.append(x + tm[1] * y - tm[0] * x)
        tm.append(y - tm[0] * y - tm[1] * x)
        #rotate the coordinate system around (x, y)
        self._transform(tm)

    def skew(self, angle_x, angle_y, x=None, y=None):
        if not x:
            x = self.x
        if not y:
            y = self.y
        if angle_x <= -90 or angle_x >= 90 or angle_y <=-90 or angle_y >=90:
            self.error('Please use angle values between -90 and 90 for skewing')
        x *= self.k
        y = (self.h - y) * self.k
        #calculate elements of transformation matrix
        tm = [1, math.tan(math.radians(angle_y)), math.tan(math.radians(angle_x)), 1]
        tm.append(-tm[2] * y)
        tm.append(-tm[1] * x)
        #skew the coordinate system
        self._transform(tm)

    def mirror_h(self, x=None):
        """scaling -100% in x-direction"""
        self.scale(-100, 100, x)

    def mirror_v(self, y=None):
        """scaling -100% in y-direction"""
        self.scale(100, -100, y=y)

    def mirror_p(self, x=None, y=None):
        """Point reflection on point (x, y). (alias for scaling -100 in x- and y-direction)"""
        self.scale(-100, -100, x, y)

    def mirror_l(self, angle=0, x=None, y=None):
        """Reflection against a straight line through point (x, y) with the gradient angle (angle)."""
        self.scale(-100, 100, x, y)
        self.rotate(-2*(angle-90), x, y)

    def skew_x(self, angle_x, x=None, y=None):
        self.skew(angle_x, 0, x, y)

    def skew_y(self, angle_y, x=None, y=None):
        self.skew(0, angle_y, x, y)

    def linear_gradient(self, x, y, w, h, col1=(), col2=(), coords=(0, 0, 1, 0)):
        self._clip(x, y, w, h)
        self._gradient(2, col1, col2, coords)

    def radial_gradient(self, x, y, w, h, col1=(), col2=(), coords=(0.5, 0.5, 0.5, 0.5, 1)):
        self._clip(x, y, w, h)
        self._gradient(3, col1, col2, coords)

    def coons_patch_mesh(self, x, y, w, h, col1=(), col2=(), col3=(), col4=(),
                        coords=(0.00, 0.0, 0.33, 0.00, 0.67, 0.00, 1.00, 0.00, 1.00, 0.33, 1.00, 0.67, 1.00, 1.00,
                                0.67, 1.00, 0.33, 1.00, 0.00, 1.00, 0.00, 0.67, 0.00, 0.33), coords_min=0,
                        coords_max=1):
        self._clip(x, y, w ,h)
        n = len(self.gradients)
        self.gradients.append({'type': 6})  #coons patch mesh
        #check the coords array if it is the simple array or the multi patch array
        if not isinstance(coords, dict):
            #simple array -> convert to multi patch array
            if len(col1) < 3:
                col1 = [col1[0], col1[1], col1[1]]
            if len(col2) < 3:
                col2 = [col2[0], col2[1], col2[1]]
            if len(col3) < 3:
                col3 = [col3[0], col3[1], col3[1]]
            if len(col4) < 3:
                col4 = [col4[0], col4[1], col4[1]]
            patch_array = [{
                'f': 0,
                'points': list(coords),
                'colors': [{'r': col1[0], 'g': col1[1], 'b': col1[2]}, {'r': col2[0], 'g': col2[1], 'b': col2[2]},
                           {'r': col3[0], 'g': col3[1], 'b': col3[2]}, {'r': col4[0], 'g': col4[1], 'b': col4[2]}]
            }]
        else:
            #multi patch array
            patch_array = coords
        bpcd = 65535 #16 BitsPerCoordinate
        #build the data stream
        stream = []
        stream_add = stream.append
        for i in xrange(len(patch_array)):
            stream_add(chr(patch_array[i]['f'])) #start with the edge flag as 8 bit
            for j in xrange(len(patch_array[i]['points'])):
                #each point as 16 bit
                patch_array[i]['points'][j] = ((patch_array[i]['points'][j] - coords_min) /
                                               (coords_max - coords_min)) * bpcd
                if patch_array[i]['points'][j] < 0:
                    patch_array[i]['points'][j] = 0
                if patch_array[i]['points'][j] > bpcd:
                    patch_array[i]['points'][j] = bpcd
                stream_add(chr(int(math.floor(patch_array[i]['points'][j] / 256.0))))
                stream_add(chr(int(math.floor(patch_array[i]['points'][j] % 256))))
            for j in xrange(len(patch_array[i]['colors'])):
                #each color component as 8 bit
                stream_add(chr(patch_array[i]['colors'][j]['r']))
                stream_add(chr(patch_array[i]['colors'][j]['g']))
                stream_add(chr(patch_array[i]['colors'][j]['b']))
        self.gradients[n]['stream'] = ''.join(stream)
        #paint the gradient
        self._out('/Sh' + str(n) + ' sh')
        #restore previous Graphic State
        self._out('Q')

    def set_line_style(self, style):
        if 'width' in style:
            width_prev = self.line_width
            self.set_line_width(style['width'])
            self.line_width = width_prev
        if 'cap' in style:
            ca = {'butt': 0, 'round': 1, 'square': 2}
            if style['cap'] in ca:
                self._out(str(ca[style['cap']]) + ' J')
        if 'join' in style:
            ja = {'miter': 0, 'round': 1, 'bevel': 2}
        if 'dash' in style:
            dash_string = ''
            if style['dash']:
                tab = style['dash'].split(',')
                dash_string = ' '.join([sprintf('%.2f', float(v)) for v in tab])
            if not('phase' in style and style['dash']):
                style['phase'] = 0
            self._out(sprintf('[%s] %.2f d', dash_string, style['phase']))
        if 'color' in style:
            r,g,b = style['color']
            self.set_draw_color(r,g,b)

    def styled_line(self, x1, y1, x2, y2, style = None):
        if style:
            self.set_line_style(style)
        self.line(x1, y1, x2, y2)

    def styled_rect(self, x, y, w, h, style='', border_style=None, fill_color=None):
        if 'F' not in style and fill_color:
            r,g,b = fill_color
            self.set_fill_color(r, g, b)
        if style == 'F':
            border_style = None
            self.rect(x, y, w, h, style)
        elif style == 'DF' or style == 'FD':
            if not border_style or 'all' in border_style:
                if 'all' in border_style:
                    self.set_line_style(border_style['all'])
                    border_style = None
                else:
                    style = 'F'
                self.rect(x, y, w, h, style)
        else:
            if not border_style or 'all' in border_style:
                if 'all' in border_style and border_style['all']:
                    self.set_line_style(border_style['all'])
                    border_style = None
                self.rect(x, y, w, h, style)

        if border_style:
            if 'L' in border_style and border_style['L']:
                self.styled_line(x, y, x, y + h, border_style['L'])
            if 'T' in border_style and border_style['T']:
                self.styled_line(x, y, x + w, y, border_style['T'])
            if 'R' in border_style and border_style['R']:
                self.styled_line(x + w, y, x + w, y + h, border_style['R'])
            if 'B' in border_style and border_style['B']:
                self.styled_line(x, y + h, x + w, y + h, border_style['B'])

    def styled_curve(self, x0, y0, x1, y1, x2, y2, x3, y3, style='', line_style=None, fill_color=None):
        if 'F' not in style and fill_color:
            r,g,b = fill_color
            self.set_fill_color(r, g, b)
        if style == 'F':
            op = 'f'
            line_style = None
        elif style == 'FD' or style == 'DF':
            op = 'B'
        else:
            op = 'S'
        if line_style:
            self.set_line_style(line_style)
        self._point(x0, y0)
        self._curve(x1, y1, x2, y2, x3, y3)
        self._out(op)

    def styled_ellipse(self, x0, y0, rx, ry=0, angle=0, a_start=0, a_finish=360, style='', line_style=None, fill_color=None,
                n_seg=8):
        if rx:
            if 'F' not in style and fill_color:
                r,g,b = fill_color
                self.set_fill_color(r, g, b)
            if style == 'F':
                op = 'f'
                line_style = None
            elif style == 'FD' or style == 'DF':
                op = 'B'
            elif style == 'C':
                op = 's'    #small 's' means closing the path as well
            else:
                op = 'S'
            if line_style:
                self.set_line_style(line_style)
            if not ry:
                ry = rx
            rx *= self.k
            ry *= self.k
            if n_seg < 2:
                n_seg = 2
            a_start = math.radians(float(a_start))
            a_finish = math.radians(float(a_finish))
            total_angle = a_finish - a_start

            dt = total_angle/n_seg
            dtm = dt/3.0

            x0 *= self.k
            y0 = (self.h - y0) * self.k
            if angle:
                a = -math.radians(float(angle))
                self._out(sprintf('q %.2f %.2f %.2f %.2f %.2f %.2f cm', math.cos(a), -1 * math.sin(a), math.sin(a),
                    math.cos(a), x0, y0))
                x0 = 0
                y0 = 0

            t1 = a_start
            a0 = x0 + (rx * math.cos(t1))
            b0 = y0 + (ry * math.sin(t1))
            c0 = -rx * math.sin(t1)
            d0 = ry * math.cos(t1)
            self._point(a0/self.k, self.h - (b0 / self.k))
            for i in xrange(1, n_seg+1):
                #Draw this bit of the total curve.
                t1 = (i * dt) + a_start
                a1 = x0 + (rx * math.cos(t1))
                b1 = y0 + (ry * math.sin(t1))
                c1 = -rx * math.sin(t1)
                d1 = ry * math.cos(t1)
                self._curve((a0 + (c0 * dtm)) / self.k, self.h - ((b0 + (d0 * dtm)) / self.k),
                    (a1 - (c1 * dtm)) / self.k, self.h - ((b1 - (d1 * dtm)) / self.k),
                    a1 / self.k, self.h - (b1 / self.k))
                a0 = a1
                b0 = b1
                c0 = c1
                d0 = d1

            self._out(op)
            if angle:
                self._out('Q')

    def styled_circle(self, x0, y0, r, a_start=0, a_finish=360, style='', line_style=None, fill_color=None, n_seg=8):
        self.styled_ellipse(x0, y0, r, 0, 0, a_start, a_finish, style, line_style, fill_color, n_seg)

    def styled_polygon(self, p, style='', line_style=None, fill_color=None):
        np = len(p) / 2
        if 'F' not in style and fill_color:
            r,g,b = fill_color
            self.set_fill_color(r, g, b)
        if style == 'F':
            line_style = None
            op = 'f'
        elif style == 'FD' or style == 'DF':
            op = 'B'
        else:
            op = 'S'
        draw = True
        if line_style:
            if 'all' in line_style:
                self.set_line_style(line_style['all'])
            else:
                #0 .. (np - 1), op = {B, S}
                draw = False
                if op == 'B':
                    op = 'f'
                    self._point(p[0], p[1])
                    for i in xrange(2, np*2, 2):
                        self._line(p[i], p[i+1])
                    self._line(p[0], p[1])
                    self._out(op)
                p[np * 2] = p[0]
                p[np * 2 + 1] = p[1]
                for i in xrange(np):
                    if i in line_style and line_style[i]:
                        self.styled_line(p[i * 2], p[(i * 2) + 1], p[(i * 2) + 2], p[(i * 2) + 3], line_style[i])
        if draw:
            self._point(p[0], p[1])
            for i in xrange(2, np*2, 2):
                self._line(p[i], p[i+1])
            self._line(p[0], p[1])
            self._out(op)

    def styled_regular_polygon(self, x0, y0, r, ns, angle=0, circle=False, style='', line_style=None,
            fill_color=None, circle_style='', circle_line_style=None, circle_fill_color=None):
        if ns < 3:
            ns = 3
        if circle:
            self.styled_circle(x0, y0, r, 0, 360, circle_style, circle_line_style, circle_fill_color)
        p = []
        p_add = p.append
        for i in xrange(ns):
            a = angle + (i * 360.0) / ns
            a_rad = math.radians(float(a))
            p_add(x0 + (r * math.sin(a_rad)))
            p_add(y0 + (r * math.cos(a_rad)))
        self.styled_polygon(p, style, line_style, fill_color)

    def styled_star_polygon(self, x0, y0, r, nv, ng, angle=0, circle=False, style = '', line_style=None,
                            fill_color=None, circle_style='', circle_line_style=None, circle_fill_color=None):
        if nv < 2:
            nv = 2
        if circle:
            self.styled_circle(x0, y0, r, 0, 360, circle_style, circle_line_style, circle_fill_color)
        p2 = []
        p2_add = p2.append
        visited = []
        visited_add = visited.append
        for i in xrange(nv):
            a = angle + (i * 360.0) / nv
            a_rad = math.radians(float(a))
            p2_add(x0 + (r * math.sin(a_rad)))
            p2_add(y0 + (r * math.cos(a_rad)))
            visited_add(False)
        p = []
        p_add = p.append
        i = 0
        p_add(p2[i * 2])
        p_add(p2[i * 2 + 1])
        visited[i] = True
        i += ng
        i %= nv
        while not visited[i]:
            p_add(p2[i * 2])
            p_add(p2[i * 2 + 1])
            visited[i] = True
            i += ng
            i %= nv
        self.styled_polygon(p, style, line_style, fill_color)

    def styled_rounded_rect(self, x, y, w, h, r, round_corner='1111', style='', border_style=None, fill_color=None):
        if round_corner == '0000':
            self.styled_rect(x, y, w, h, style, border_style, fill_color)
        else:
            if 'F' not in style and fill_color:
                red,g,b = fill_color
                self.set_fill_color(red, g, b)
            if style == 'F':
                border_style = None
                op = 'f'
            elif style == 'DF' or style == 'FD':
                op = 'B'
            else:
                op = 'S'
            if border_style:
                self.set_line_style(border_style)
            my_arc = 4.0 / 3.0 * (math.sqrt(2) - 1)
            self._point(x + r, y)
            xc = x + w - r
            yc = y + r
            self._line(xc, y)
            if round_corner[0] == '1':
                self._curve(xc + (r * my_arc), yc - r, xc + r, yc - (r * my_arc), xc + r, yc)
            else:
                self._line(x + w, y)

            xc = x + w - r
            yc = y + h - r
            self._line(x + w, yc)
            if round_corner[1] == '1':
                self._curve(xc + r, yc + (r * my_arc), xc + (r * my_arc), yc + r, xc, yc + r)
            else:
                self._line(x + w, y + h)

            xc = x + r
            yc = y + h - r
            self._line(xc, y + h)
            if round_corner[2] == '1':
                self._curve(xc - (r * my_arc), yc + r, xc - r, yc + (r * my_arc), xc - r, yc)
            else:
                self._line(x, y + h)

            xc = x + r
            yc = y + r
            self._line(x ,yc)
            if round_corner[3] == '1':
                self._curve(xc - r, yc - (r * my_arc), xc - (r * my_arc), yc - r, xc, yc - r)
            else:
                self._line(x, y)
                self._line(x + r, y)
            self._out(op)

    def code128(self, x, y, code, w, h):
        T128 = [
            (2, 1, 2, 2, 2, 2),          #0 : [ ]
            (2, 2, 2, 1, 2, 2),          #1 : [!]
            (2, 2, 2, 2, 2, 1),          #2 : ["]
            (1, 2, 1, 2, 2, 3),          #3 : [#]
            (1, 2, 1, 3, 2, 2),          #4 : [$]
            (1, 3, 1, 2, 2, 2),          #5 : [%]
            (1, 2, 2, 2, 1, 3),          #6 : [&]
            (1, 2, 2, 3, 1, 2),          #7 : [']
            (1, 3, 2, 2, 1, 2),          #8 : [(]
            (2, 2, 1, 2, 1, 3),          #9 : [)]
            (2, 2, 1, 3, 1, 2),          #10 : [*]
            (2, 3, 1, 2, 1, 2),          #11 : [+]
            (1, 1, 2, 2, 3, 2),          #12 : [,]
            (1, 2, 2, 1, 3, 2),          #13 : [-]
            (1, 2, 2, 2, 3, 1),          #14 : [.]
            (1, 1, 3, 2, 2, 2),          #15 : [/]
            (1, 2, 3, 1, 2, 2),          #16 : [0]
            (1, 2, 3, 2, 2, 1),          #17 : [1]
            (2, 2, 3, 2, 1, 1),          #18 : [2]
            (2, 2, 1, 1, 3, 2),          #19 : [3]
            (2, 2, 1, 2, 3, 1),          #20 : [4]
            (2, 1, 3, 2, 1, 2),          #21 : [5]
            (2, 2, 3, 1, 1, 2),          #22 : [6]
            (3, 1, 2, 1, 3, 1),          #23 : [7]
            (3, 1, 1, 2, 2, 2),          #24 : [8]
            (3, 2, 1, 1, 2, 2),          #25 : [9]
            (3, 2, 1, 2, 2, 1),          #26 : [:]
            (3, 1, 2, 2, 1, 2),          #27 : [;]
            (3, 2, 2, 1, 1, 2),          #28 : [<]
            (3, 2, 2, 2, 1, 1),          #29 : [=]
            (2, 1, 2, 1, 2, 3),          #30 : [>]
            (2, 1, 2, 3, 2, 1),          #31 : [?]
            (2, 3, 2, 1, 2, 1),          #32 : [@]
            (1, 1, 1, 3, 2, 3),          #33 : [A]
            (1, 3, 1, 1, 2, 3),          #34 : [B]
            (1, 3, 1, 3, 2, 1),          #35 : [C]
            (1, 1, 2, 3, 1, 3),          #36 : [D]
            (1, 3, 2, 1, 1, 3),          #37 : [E]
            (1, 3, 2, 3, 1, 1),          #38 : [F]
            (2, 1, 1, 3, 1, 3),          #39 : [G]
            (2, 3, 1, 1, 1, 3),          #40 : [H]
            (2, 3, 1, 3, 1, 1),          #41 : [I]
            (1, 1, 2, 1, 3, 3),          #42 : [J]
            (1, 1, 2, 3, 3, 1),          #43 : [K]
            (1, 3, 2, 1, 3, 1),          #44 : [L]
            (1, 1, 3, 1, 2, 3),          #45 : [M]
            (1, 1, 3, 3, 2, 1),          #46 : [N]
            (1, 3, 3, 1, 2, 1),          #47 : [O]
            (3, 1, 3, 1, 2, 1),          #48 : [P]
            (2, 1, 1, 3, 3, 1),          #49 : [Q]
            (2, 3, 1, 1, 3, 1),          #50 : [R]
            (2, 1, 3, 1, 1, 3),          #51 : [S]
            (2, 1, 3, 3, 1, 1),          #52 : [T]
            (2, 1, 3, 1, 3, 1),          #53 : [U]
            (3, 1, 1, 1, 2, 3),          #54 : [V]
            (3, 1, 1, 3, 2, 1),          #55 : [W]
            (3, 3, 1, 1, 2, 1),          #56 : [X]
            (3, 1, 2, 1, 1, 3),          #57 : [Y]
            (3, 1, 2, 3, 1, 1),          #58 : [Z]
            (3, 3, 2, 1, 1, 1),          #59 : [[]
            (3, 1, 4, 1, 1, 1),          #60 : [\]
            (2, 2, 1, 4, 1, 1),          #61 : []]
            (4, 3, 1, 1, 1, 1),          #62 : [^]
            (1, 1, 1, 2, 2, 4),          #63 : [_]
            (1, 1, 1, 4, 2, 2),          #64 : [`]
            (1, 2, 1, 1, 2, 4),          #65 : [a]
            (1, 2, 1, 4, 2, 1),          #66 : [b]
            (1, 4, 1, 1, 2, 2),          #67 : [c]
            (1, 4, 1, 2, 2, 1),          #68 : [d]
            (1, 1, 2, 2, 1, 4),          #69 : [e]
            (1, 1, 2, 4, 1, 2),          #70 : [f]
            (1, 2, 2, 1, 1, 4),          #71 : [g]
            (1, 2, 2, 4, 1, 1),          #72 : [h]
            (1, 4, 2, 1, 1, 2),          #73 : [i]
            (1, 4, 2, 2, 1, 1),          #74 : [j]
            (2, 4, 1, 2, 1, 1),          #75 : [k]
            (2, 2, 1, 1, 1, 4),          #76 : [l]
            (4, 1, 3, 1, 1, 1),          #77 : [m]
            (2, 4, 1, 1, 1, 2),          #78 : [n]
            (1, 3, 4, 1, 1, 1),          #79 : [o]
            (1, 1, 1, 2, 4, 2),          #80 : [p]
            (1, 2, 1, 1, 4, 2),          #81 : [q]
            (1, 2, 1, 2, 4, 1),          #82 : [r]
            (1, 1, 4, 2, 1, 2),          #83 : [s]
            (1, 2, 4, 1, 1, 2),          #84 : [t]
            (1, 2, 4, 2, 1, 1),          #85 : [u]
            (4, 1, 1, 2, 1, 2),          #86 : [v]
            (4, 2, 1, 1, 1, 2),          #87 : [w]
            (4, 2, 1, 2, 1, 1),          #88 : [x]
            (2, 1, 2, 1, 4, 1),          #89 : [y]
            (2, 1, 4, 1, 2, 1),          #90 : [z]
            (4, 1, 2, 1, 2, 1),          #91 : [{]
            (1, 1, 1, 1, 4, 3),          #92 : [|]
            (1, 1, 1, 3, 4, 1),          #93 : [}]
            (1, 3, 1, 1, 4, 1),          #94 : [~]
            (1, 1, 4, 1, 1, 3),          #95 : [DEL]
            (1, 1, 4, 3, 1, 1),          #96 : [FNC3]
            (4, 1, 1, 1, 1, 3),          #97 : [FNC2]
            (4, 1, 1, 3, 1, 1),          #98 : [SHIFT]
            (1, 1, 3, 1, 4, 1),          #99 : [Cswap]
            (1, 1, 4, 1, 3, 1),          #100 : [Bswap]
            (3, 1, 1, 1, 4, 1),          #101 : [Aswap]
            (4, 1, 1, 1, 3, 1),          #102 : [FNC1]
            (2, 1, 1, 4, 1, 2),          #103 : [Astart]
            (2, 1, 1, 2, 1, 4),          #104 : [Bstart]
            (2, 1, 1, 2, 3, 2),          #105 : [Cstart]
            (2, 3, 3, 1, 1, 1),          #106 : [STOP]
            (2, 1),                      #107 : [END BAR]
        ]
        j_start = {"A": 103, "B": 104, "C": 105}
        j_swap = {"A": 101, "B": 100, "C": 99}
        abc_set = []
        for i in xrange(32, 96):
            abc_set.append(chr(i))
        a_set = abc_set[:]
        b_set = abc_set[:]
        for i in xrange(32):
            abc_set.append(chr(i))
            a_set.append(chr(i))
        for i in xrange(96, 127):
            abc_set.append(chr(i))
            b_set.append(chr(i))
        sets = {'A':{}, 'B':{}}
        for i in xrange(96):
            sets['A'][chr(i)] = chr(i + 64) if i < 32 else chr(i - 32)
            sets['B'][chr(i+32)] = chr(i)
        c_set = '0123456789'
        a_guid = []
        b_guid = []
        c_guid = []
        for i in xrange(len(code)):
            needle = code[i]
            a_guid.append('N' if needle not in a_set else 'O')
            b_guid.append('N' if needle not in b_set else 'O')
            c_guid.append('N' if needle not in c_set else 'O')
        s_mini_c = 'OOOO'
        i_mini_c = 4
        crypt = []
        while code > '':
            c_guid_str = ''.join(c_guid)
            i = c_guid_str.find(s_mini_c)
            if i > -1:
                a_guid[i] = 'N'
                b_guid[i] = 'N'
            a_guid_str = ''.join(a_guid)
            b_guid_str = ''.join(b_guid)
            if c_guid_str[:i_mini_c] == s_mini_c:
                crypt.append(chr(j_swap['C']) if len(crypt) else chr(j_start['C']))
                made = c_guid_str.find('N')
                if made == -1:
                    made = len(c_guid_str)
                if math.fmod(made,2) == 1:
                    made -= 1
                for i in xrange(0, made, 2):
                    crypt.append(chr(int(code[i:i+2])))
                jeu = 'C'
            else:
                made_a = a_guid_str.find('N')
                if made_a == -1:
                    made_a = len(a_guid_str)
                made_b = b_guid_str.find('N')
                if made_b == -1:
                    made_b = len(b_guid_str)
                made = made_b if made_a <  made_b else made_a
                jeu = 'B' if made_a < made_b else 'A'
                crypt.append(chr(j_swap[jeu]) if len(crypt) else chr(j_start[jeu]))
                for j in code[:made]:
                    crypt.append(sets[jeu][j])
            code = code[made:]
            a_guid = a_guid[made:]
            b_guid = b_guid[made:]
            c_guid = c_guid[made:]
        crypt_str = ''.join(crypt)
        check = ord(crypt_str[0])
        for i in xrange(len(crypt_str)):
            check += ord(crypt_str[i]) * i
        check %= 103
        crypt.append(chr(check))
        crypt.append(chr(106))
        crypt.append(chr(107))
        crypt_str = ''.join(crypt)
        i = len(crypt_str) * 11 - 8
        modul = w * 1.0 / i
        for i in xrange(len(crypt_str)):
            c = T128[ord(crypt_str[i])]
            j = 0
            while j < len(c) - 1:
                self.rect(x, y , c[j]*modul, h, 'F')
                x += (c[j+1] + c[j]) * modul
                j += 2

        return crypt_str

# ******************************************************************************
# *                                                                              *
# *                              Protected methods                               *
# *                                                                              *
# *******************************************************************************/
    def _dochecks(self):
        """Check for locale-related bug"""
#        if 1.1 == 1:
#            self.error("Don\'t alter the locale before including class file")
        #Check for decimal separator
        if sprintf('%.1f', 1.0) != '1.0':
            import locale
            locale.setlocale(locale.LC_NUMERIC,'C')

    def _getfontpath(self):
        """Local font dir path"""
        return FPDF_FONT_DIR

    def _getpagesize(self, size):
        """Get the page size"""
        if isinstance(size,basestring):
            size = size.lower()
            if size not in self.std_page_sizes:
                self.error('Unknown page size: ' + size)
            a = self.std_page_sizes[size]
            return a[0]/self.k, a[1]/self.k
        elif isinstance(size,(list,set,tuple)) and len(size) == 2:
            if size[0] > size[1]:
                return size[1], size[0]
            else:
                return size[0], size[1]
        else:
            self.error('Unknown page size: {0}'.format(size))

    def _beginpage(self, orientation, size):
        """Starts a new pdf page"""
        self.page += 1
        self.pages[self.page] = ''
        self.state = 2
        self.x = self.l_margin
        self.y = self.t_margin
        self.font_family = ''
        #Check page size and orientation
        if orientation == '':
            orientation = self.def_orientation
        else:
            orientation = orientation[0].upper()
        if size == '':
            size = self.def_page_size
        else:
            size = self._getpagesize(size)
        if orientation != self.cur_orientation or size[0] != self.cur_page_size[0] or size != self.cur_page_size[1]:
            #New size or orientation
            if orientation == 'P':
                self.w = size[0]
                self.h = size[1]
            else:
                self.w = size[1]
                self.h = size[0]
            self.w_pt = self.w * self.k
            self.h_pt = self.h * self.k
            self.page_break_trigger = self.h - self.b_margin
            self.cur_orientation = orientation
            self.cur_page_size = size

        if orientation != self.def_orientation or size[0] != self.def_page_size[0] or size[1] != self.def_page_size[1]:
            self.page_sizes[self.page] = (self.w_pt,  self.h_pt)

    def _endpage(self):
        """End of page contents"""
        self.state = 1

    def _loadfont(self, font):
        """Load a font definition file from the font directory"""
        a = {}
        execfile(os.path.join(self._getfontpath(), font), globals(), a)
        if 'name' not in a:
            self.error('Could not include font definition file "{0}"'.format(font))
        return a

    def _escape(self, s):
        """Add \ before \r, \, ( and )"""
        return s.replace('\\','\\\\').replace(')','\\)').replace('(','\\(').replace('\r','\\r')

    def _textstring(self, s):
        """Format a text string"""
        if self.encrypted:
            s = self._rc4(self._objectkey(self.n), s)
        return '(' + self._escape(s) + ')'

    def _UTF8_to_UTF16(self,s):
        """Convert UTF-8 to UTF-16BE with BOM"""
        res = ['\xFE\xFF']
        add = res.append
        nb = len(s)
        i = 0
        while i<nb:
            i += 1
            c1 = ord(s[i])
            if c1>224:
                # 3-byte character
                i += 1
                c2 = ord(s[i])
                i += 1
                c3 = ord(s[i])
                add(chr(((c1 & 0x0F)<<4)+((c2 & 0x3C)>>2)))
                add(chr(((c2 & 0x03)<<6)+(c3 & 0x3F)))
            elif c1>=192:
                #2-byte character
                i += 1
                c2 = ord(s[i])
                add(chr((c1 & 0x1C)>>2))
                add(chr(((c1 & 0x03)<<6) + (c2 & 0x3F)))
            else:
                #Single-byte character
                add('\0'+chr(c1))
        return ''.join(res)

    def _dounderline(self, x, y, txt):
        """Underline text"""
        up = self.current_font['up']
        ut = self.current_font['ut']
        w = self.get_string_width(txt) + self.ws * txt.count(' ')
        return sprintf('%.2f %.2f %.2f %.2f re f',x * self.k, (self.h - (y - up / 1000.0 * self.font_size)) * self.k,
            w * self.k, - ut / 1000.0 * self.font_size_pt)

    def _parsejpg(self, filename):
        """ Extract info from a JPEG file"""
        if Image is None:
            self.error('PIL not installed')
        try:
            f = open(filename, 'rb')
            im = Image.open(f)
        except Exception, e:
            self.error('Missing or incorrect image file: %s. error: %s' % (filename, str(e)))
        else:
            a = im.size
            # We shouldn't get into here, as Jpeg is RGB=8bpp right(?), but, just in case...
        bpc=8
        if im.mode == 'RGB':
            colspace='DeviceRGB'
        elif im.mode == 'CMYK':
            colspace='DeviceCMYK'
        else:
            colspace='DeviceGray'

        # Read whole file from the start
        f.seek(0)
        data = f.read()
        f.close()
        return {'w':a[0],'h':a[1],'cs':colspace,'bpc':bpc,'f':'DCTDecode','data':data}

    def _parsepng(self, name):
        """Extract info from a PNG file"""
        if name.startswith("http://") or name.startswith("https://"):
            import urllib
            f = urllib.urlopen(name)
        else:
            f=open(name,'rb')
        if not f:
            self.error("Can't open image file: " + name)
        #Check signature
        if f.read(8) != '\x89' + 'PNG' + '\r' + '\n' + '\x1a' + '\n':
            self.error('Not a PNG file: ' + name)
        #Read header chunk
        f.read(4)
        if f.read(4) != 'IHDR':
            self.error('Incorrect PNG file: ' + name)
        w = self._freadint(f)
        h = self._freadint(f)
        bpc = ord(f.read(1))
        if bpc > 8:
            self.error('16-bit depth not supported: ' + name)
        ct = ord(f.read(1))
        if ct == 0:
            colspace = 'DeviceGray'
        elif ct == 2:
            colspace = 'DeviceRGB'
        elif ct == 3:
            colspace = 'Indexed'
        else:
            self.error('Alpha channel not supported: ' + name)
        if ord(f.read(1)) != 0:
            self.error('Unknown compression method: ' + name)
        if ord(f.read(1)) != 0:
            self.error('Unknown filter method: ' + name)
        if ord(f.read(1)) != 0:
            self.error('Interlacing not supported: ' + name)
        f.read(4)
        parms = '/DecodeParms <</Predictor 15 /Colors '
        if ct == 2:
            parms += '3'
        else:
            parms += '1'
        parms +=' /BitsPerComponent ' + str(bpc) + ' /Columns ' + str(w) + '>>'
        #Scan chunks looking for palette, transparency and image data
        pal = ''
        trns = ''
        data = ''
        n = 1
        while n != None:
            n = self._freadint(f)
            type = f.read(4)
            if type == 'PLTE':
                #Read palette
                pal=f.read(n)
                f.read(4)
            elif type == 'tRNS':
                #Read transparency info
                t = f.read(n)
                if ct == 0:
                    trns = [ord(substr(t, 1, 1)),]
                elif ct == 2:
                    trns = [ord(substr(t, 1, 1)), ord(substr(t, 3, 1)), ord(substr(t, 5, 1))]
                else:
                    pos = t.find('\x00')
                    if pos != -1:
                        trns = [pos,]
                f.read(4)
            elif type=='IDAT':
                #Read image data block
                data += f.read(n)
                f.read(4)
            elif type == 'IEND':
                break
            else:
                f.read(n+4)
        if colspace == 'Indexed' and not pal:
            self.error('Missing palette in ' + name)
        f.close()
        return {'w':w,'h':h,'cs':colspace,'bpc':bpc,'f':'FlateDecode','parms':parms,'pal':pal,'trns':trns,'data':data}

    def _freadint(self, f):
        """Read a 4-byte integer from file"""
        try:
            return struct.unpack('>HH',f.read(4))[1]
        except:
            return None

    def _newobj(self):
        """Begin a new object"""
        self.n += 1
        self.offsets[self.n] = len(self.buffer)
        self._out(str(self.n) + ' 0 obj')

    def _putstream(self, s):
        if self.encrypted:
            s = self._rc4(self._objectkey(self.n), s)
        self._out('stream')
        self._out(s)
        self._out('endstream')

    def _out(self, s):
        """Add a line to the document"""
        if self.state == 2:
            self.pages[self.page] += s + "\n"
        else:
            self.buffer += str(s) + "\n"

    def _putpages(self):
        """Add each page content to the pdf"""
        nb = self.page
        if hasattr(self, 'str_alias_nb_pages'):
            # Replace number of pages in fonts using subsets
            alias = self.UTF8_to_UTF16BE(self.str_alias_nb_pages, False)
            r = self.UTF8_to_UTF16BE(str(nb), False)
            for n in xrange(1, nb + 1):
                self.pages[n] = self.pages[n].replace(alias, r)
            #Now repeat for no pages in non-subset fonts
            for n in xrange(1, nb + 1):
                self.pages[n] = self.pages[n].replace(self.str_alias_nb_pages, str(nb))
        if self.def_orientation =='P':
            w_pt=self.def_page_size[0] * self.k
            h_pt=self.def_page_size[1] * self.k
        else:
            w_pt=self.def_page_size[1] * self.k
            h_pt=self.def_page_size[0] * self.k
        if self.compress:
            filter = '/Filter /FlateDecode '
        else:
            filter = ''
        for n in xrange(1,nb+1):
            #Page
            self._newobj()
            self._out('<</Type /Page')
            self._out('/Parent 1 0 R')
            if n in self.page_sizes:
                self._out(sprintf('/MediaBox [0 0 %.2f %.2f]', self.page_sizes[n][0], self.page_sizes[n][1]))
            self._out('/Resources 2 0 R')
            if self.page_links and n in self.page_links:
                #Links
                annots='/Annots ['
                for pl in self.page_links[n]:
                    rect = sprintf('%.2f %.2f %.2f %.2f', pl[0], pl[1], pl[0]+pl[2], pl[1]-pl[3])
                    annots += '<</Type /Annot /Subtype /Link /Rect [' + rect + '] /Border [0 0 0] '
                    if isinstance(pl[4], basestring):
                        annots+='/A <</S /URI /URI ' + self._textstring(pl[4]) + '>>>>'
                    else:
                        l = self.links[pl[4]]
                        if l[0] in self.page_sizes:
                            h = self.page_sizes[l[0]][1]
                        else:
                            h = h_pt
                        annots += sprintf('/Dest [%d 0 R /XYZ 0 %.2f null]>>', 1 + 2 * l[0], h-l[1] * self.k)
                self._out(annots + ']')
            if self.pdf_version > '1.3':
                self._out('/Group <</Type /Group /S /Transparency /CS /DeviceRGB>>')
            self._out('/Contents ' + str(self.n+1) + ' 0 R>>')
            self._out('endobj')
            #Page content
            if self.compress:
                p = zlib.compress(self.pages[n])
            else:
                p = self.pages[n]
            self._newobj()
            self._out('<<' + filter + '/Length ' + str(len(p)) + '>>')
            self._putstream(p)
            self._out('endobj')
        #Pages root
        self.offsets[1] =  len(self.buffer)
        self._out('1 0 obj')
        self._out('<</Type /Pages')
        kids='/Kids ['
        for i in xrange(0,nb):
            kids += str(3 + 2 * i) + ' 0 R '
        self._out(kids+']')
        self._out('/Count '+str(nb))
        self._out(sprintf('/MediaBox [0 0 %.2f %.2f]', w_pt, h_pt))
        self._out('>>')
        self._out('endobj')

    def _putfonts(self):
        """Add fonts to the pdf file"""
        nf = self.n
        for diff in self.diffs:
            #Encodings
            self._newobj()
            self._out('<</Type /Encoding /BaseEncoding /WinAnsiEncoding /Differences [' + self.diffs[diff] + ']>>')
            self._out('endobj')
        for font_file,info in self.font_files.iteritems():
            if 'type' not in info or info['type'] != 'TTF':
                #Font file embedding
                self._newobj()
                self.font_files[font_file]['n'] = self.n
                font = ''
                f = file(os.path.join(self._getfontpath(), font_file), 'rb', 1)
                if not f:
                    self.error('Font file not found')
                font = f.read()
                f.close()
                compressed = (substr(font_file, -2) == '.z')
                if not compressed and 'length2' in info:
                    header = (ord(font[0])==128)
                    if(header):
                        #Strip first binary header
                        font = substr(font, 6)
                    if header and ord(font[info['length1']]) == 128:
                        #Strip second binary header
                        font = substr(font, 0, info['length1']) + substr(font, info['length1'] + 6)
                self._out('<</Length ' + str(len(font)))
                if compressed:
                    self._out('/Filter /FlateDecode')
                self._out('/Length1 ' + str(info['length1']))
                if'length2' in info:
                    self._out('/Length2 ' + str(info['length2']) + ' /Length3 0')
                self._out('>>')
                self._putstream(font)
                self._out('endobj')

        for k,font in self.fonts.iteritems():
            #Font objects
#            self.fonts[k]['n']=self.n+1
            type = font['type']
            name = font['name']
            if type=='Core':
                #Standard font
                self.fonts[k]['n'] = self.n + 1
                self._newobj()
                self._out('<</Type /Font')
                self._out('/BaseFont /'+name)
                self._out('/Subtype /Type1')
                if name != 'Symbol' and name != 'ZapfDingbats':
                    self._out('/Encoding /WinAnsiEncoding')
                self._out('>>')
                self._out('endobj')
            elif type == 'Type1' or type == 'TrueType':
                #Additional Type1 or TrueType font
                self.fonts[k]['n'] = self.n + 1
                self._newobj()
                self._out('<</Type /Font')
                self._out('/BaseFont /' + name)
                self._out('/Subtype /' + type)
                self._out('/FirstChar 32 /LastChar 255')
                self._out('/Widths ' + str(self.n+1) + ' 0 R')
                self._out('/FontDescriptor ' + str(self.n + 2) + ' 0 R')
                if font['enc']:
                    if 'diff' in font and font['diff']:
                        self._out('/Encoding ' + str(nf) + font['diff'] + ' 0 R')
                    else:
                        self._out('/Encoding /WinAnsiEncoding')
                self._out('>>')
                self._out('endobj')
                #Widths
                self._newobj()
                cw = font['cw']
                s='['
                for i in xrange(32,256):
                    # Get doesn't rise exception; returns 0 instead of None if not set
                    s += str(cw.get(chr(i)) or 0) + ' '
                self._out(s+']')
                self._out('endobj')
                #Descriptor
                self._newobj()
                s = '<</Type /FontDescriptor /FontName /' + name
                for k,v in font['desc'].iteritems():
                    s += ' /' + str(k) + ' ' + str(v)
                filename=font['file']
                if filename:
                    s += ' /FontFile'
                    if type != 'Type1':
                        s += '2'
                    s += ' ' + str(self.font_files[filename]['n']) + ' 0 R'
                self._out(s+'>>')
                self._out('endobj')
                #TrueType embedded SUBSETS or FULL
            elif type == 'TTF':
                self.fonts[k]['n'] = self.n + 1
                from font.unitfont import TTFontFile
                ttf = TTFontFile()
                font_name = 'MPDFAA' + '+' + font['name']
                subset = font['subset']
                if 0 in subset:
                    del subset[0]
                ttf_font_stream = ttf.make_subset(font['ttffile'], subset)
                ttf_font_size = len(ttf_font_stream)
                font_stream = zlib.compress(ttf_font_stream)
                code_to_glyph = ttf.code_to_glyph
                if 0 in code_to_glyph:
                    del code_to_glyph[0]

                #// Type0 Font
                #// A composite font - a font composed of other fonts, organized hierarchically
                self._newobj()
                self._out('<</Type /Font')
                self._out('/Subtype /Type0')
                self._out('/BaseFont /' + font_name)
                self._out('/Encoding /Identity-H')
                self._out('/DescendantFonts [' + str(self.n + 1) + ' 0 R]')
                self._out('/ToUnicode ' + str(self.n + 2) + ' 0 R')
                self._out('>>')
                self._out('endobj')

                #// CIDFontType2
                #// A CIDFont whose glyph descriptions are based on TrueType font technology
                self._newobj()
                self._out('<</Type /Font')
                self._out('/Subtype /CIDFontType2')
                self._out('/BaseFont /' + font_name)
                self._out('/CIDSystemInfo ' + str(self.n + 2) + ' 0 R')
                self._out('/FontDescriptor ' + str(self.n + 3) + ' 0 R')
                if 'desc' in font and 'MissingWidth' in font['desc']:
                    self._out('/DW ' + str(font['desc']['MissingWidth']))

                self._putTTfontwidths(font, ttf.max_uni)

                self._out('/CIDToGIDMap ' + str(self.n + 4) + ' 0 R')
                self._out('>>')
                self._out('endobj')

                #// ToUnicode
                self._newobj()
                to_uni = "/CIDInit /ProcSet findresource begin\n"
                to_uni += "12 dict begin\n"
                to_uni += "begincmap\n"
                to_uni += "/CIDSystemInfo\n"
                to_uni += "<</Registry (Adobe)\n"
                to_uni += "/Ordering (UCS)\n"
                to_uni += "/Supplement 0\n"
                to_uni += ">> def\n"
                to_uni += "/CMapName /Adobe-Identity-UCS def\n"
                to_uni += "/CMapType 2 def\n"
                to_uni += "1 begincodespacerange\n"
                to_uni += "<0000> <FFFF>\n"
                to_uni += "endcodespacerange\n"
                to_uni += "1 beginbfrange\n"
                to_uni += "<0000> <FFFF> <0000>\n"
                to_uni += "endbfrange\n"
                to_uni += "endcmap\n"
                to_uni += "CMapName currentdict /CMap defineresource pop\n"
                to_uni += "end\n"
                to_uni += "end"
                self._out('<</Length ' + str(len(to_uni)) + '>>')
                self._putstream(to_uni)
                self._out('endobj')

                #CIDSystemInfo dictionary
                self._newobj()
                self._out('<</Registry (Adobe)')
                self._out('/Ordering (UCS)')
                self._out('/Supplement 0')
                self._out('>>')
                self._out('endobj')

                #Font descriptor
                self._newobj()
                self._out('<</Type /FontDescriptor')
                self._out('/FontName /'+ font_name)
                for kd, v in font['desc'].iteritems():
                    if kd.lower() == 'flags':
                        v |= 4
                        v &= ~32    #SYMBOLIC font flag
                    self._out(' /' + kd + ' ' + str(v))

                self._out('/FontFile2 ' + str(self.n + 2) + ' 0 R')
                self._out('>>')
                self._out('endobj')

                #// Embed CIDToGIDMap
                #// A specification of the mapping from CIDs to glyph indices
                cid_to_gidmap = ["\x00" for _i in xrange(256*256*2)]
                for cc, glyph in code_to_glyph.iteritems():
                    cid_to_gidmap[cc * 2] = chr(glyph >> 8)
                    cid_to_gidmap[cc * 2 + 1] = chr(glyph & 0xFF)
                cid_to_gidmap = zlib.compress(''.join(cid_to_gidmap))
                self._newobj()
                self._out('<</Length ' + str(len(cid_to_gidmap)))
                self._out('/Filter /FlateDecode')
                self._out('>>')
                self._putstream(cid_to_gidmap)
                self._out('endobj')

                # //Font file
                self._newobj()
                self._out('<</Length ' + str(len(font_stream)))
                self._out('/Filter /FlateDecode')
                self._out('/Length1 ' + str(ttf_font_size))
                self._out('>>')
                self._putstream(font_stream)
                self._out('endobj')
                del ttf
            else:
                #Allow for additional types
                mtd = '_put' + type.lower()
                if not(hasattr(self, mtd) and callable(getattr(self, mtd))):
                    self.error('Unsupported font type: '+type)
                self.mtd(font)

    def _putTTfontwidths(self, font, max_uni):
        if os.path.exists(font['unifilename']+'.cw127.py'):
            imports = {}
            execfile(font['unifilename']+'.cw127.py', globals(), imports)
            range_id = imports['range_id']
            range = imports['range']
            prev_cid = imports['prev_cid']
            prev_width = imports['prev_width']
            interval = imports['interval']
            start_cid = 128
            del imports
        else:
            range_id = 0
            range = {}
            prev_cid = -2
            prev_width = -1
            interval = False
            start_cid = 1

        cw_len = max_uni + 1
        #for each character
        for cid in xrange(start_cid,cw_len):
            if cid == 128 and  not os.path.exists(font['unifilename']+'.cw127.py'):
                if os.access(os.path.join(self._getfontpath(), 'unitfont'), os.W_OK):
                    fh = open(font['unifilename']+'.cw127.py', 'wb')
                    cw127 = "\n".join([
                        'range_id = {0}'.format(range_id),
                        'prev_cid = {0}'.format(prev_cid),
                        'prev_width = {0}'.format(prev_width)
                    ])
                    if interval:
                        cw127 += "\ninterval = True"
                    else:
                        cw127 +="\ninterval = False"
                    cw127 += "\nrange = {0}".format(range)
                    fh.write(cw127)
                    fh.close()

            if font['cw'][cid*2] == "\00" and font['cw'][cid*2+1] == "\00":
                continue
            width = (ord(font['cw'][cid*2]) << 8) + ord(font['cw'][cid*2+1])
            if width == 65535:
                width = 0
            if cid > 255 and (cid not in font['subset'] or not font['subset'][cid]):
                continue
            if 'dw' not in font or 'dw' in font and width != font['dw']:
                if cid == prev_cid + 1:
                    if width == prev_width:
                        if width == range[range_id][0]:
                            idx = max(set(range[range_id].keys()) - {'interval'}) + 1
                            range[range_id][idx] = width
                        else:
                            #new range
                            idx = max(set(range[range_id].keys()) - {'interval'})
                            del range[range_id][idx]
                            range_id = prev_cid
                            range[range_id] = {0:prev_width, 1:width}
                        interval = True
                        range[range_id]['interval'] = True
                    else:
                        if interval:
                            #new range
                            range_id = cid
                            range[range_id] = {0:width}
                        else:
                            idx = max(set(range[range_id].keys()) - {'interval'}) + 1
                            range[range_id][idx] = width
                        interval = False
                else:
                    range_id = cid
                    range[range_id] = {0:width}
                    interval = False
                prev_cid = cid
                prev_width = width

        prev_k = -1
        next_k = -1
        prev_int = False
        for k in sorted(range):
            ws = range[k].keys()
            cws = len(ws)
            if (k == next_k) and (not prev_int) and ('interval' not in ws or cws < 4):
                if 'interval' in range[k]:
                    del range[k]['interval']
                idx = max(set(range[prev_k].keys()) - {'interval'}) + 1
                for el in range[k]:
                    range[prev_k][idx] = range[k][el]
                    idx += 1
                del range[k]
            else:
                prev_k = k

            next_k = k + cws
            if 'interval' in ws:
                if cws > 3:
                    prev_int = True
                else:
                    prev_int = False
                if k in range and 'interval' in range[k]:
                    del range[k]['interval']
                next_k -= 1
            else:
                prev_int = False

        w = 0
        w_list = []
        w_list_add = w_list.append
        for k in sorted(range):
            ws = range[k]
            values = set(ws.values())
            if len(values) == 1:
                w_list_add(' {0} {1} {2}'.format(k, k + len(ws) - 1, ws[0]))
            else:
                w_list_add(" {0} [ {1} ]\n".format(k, ' '.join([str(ws[x]) for x in ws])))
        w = ''.join(w_list)
        self._out('/W [' + w + ' ]')

    def _putimages(self):
        filter = ''
        if self.compress:
            filter = '/Filter /FlateDecode '
        for filename,info in self.images.iteritems():
            self._newobj()
            self.images[filename]['n']=self.n
            self._out('<</Type /XObject')
            self._out('/Subtype /Image')
            self._out('/Width '+str(info['w']))
            self._out('/Height '+str(info['h']))
            if info['cs'] == 'Indexed':
                self._out('/ColorSpace [/Indexed /DeviceRGB '+str(len(info['pal'])/3-1)+' '+str(self.n+1)+' 0 R]')
            else:
                self._out('/ColorSpace /'+info['cs'])
                if info['cs'] == 'DeviceCMYK':
                    self._out('/Decode [1 0 1 0 1 0 1 0]')
            self._out('/BitsPerComponent '+str(info['bpc']))
            if 'f' in info:
                self._out('/Filter /'+info['f'])
            if 'parms' in info:
                self._out(info['parms'])
            if 'trns' in info and isinstance(info['trns'],list):
                trns = ''
                for i in xrange(0,len(info['trns'])):
                    trns += str(info['trns'][i]) + ' ' + str(info['trns'][i]) + ' '
                self._out('/Mask ['+trns+']')
            self._out('/Length ' + str(len(info['data'])) + '>>')
            self._putstream(info['data'])
            self.images[filename]['data'] = None
            self._out('endobj')
            #Palette
            if info['cs'] == 'Indexed':
                self._newobj()
                if self.compress:
                    pal = zlib.compress(info['pal'])
                else:
                    pal = info['pal']
                self._out('<<' + filter + '/Length ' + str(len(pal)) + '>>')
                self._putstream(pal)
                self._out('endobj')

    def _putxobjectdict(self):
        for image in self.images.values():
            self._out('/I' + str(image['i']) + ' ' + str(image['n']) + ' 0 R')

    def _putresourcedict(self):
        self._out('/ProcSet [/PDF /Text /ImageB /ImageC /ImageI]')
        self._out('/Font <<')
        for font in self.fonts.values():
            self._out('/F' + str(font['i']) + ' ' + str(font['n']) + ' 0 R')
        self._out('>>')
        self._out('/XObject <<')
        self._putxobjectdict()
        self._out('>>')
        if len(self.gradients):
            self._out('/Shading <<')
            for id, grad in enumerate(self.gradients):
                self._out('/Sh' + str(id) + ' ' + str(grad['id']) + ' 0 R')
            self._out('>>')

    def _putresources(self):
        if len(self.gradients):
            self._putshaders()

        self._putfonts()
        self._putimages()
        #Resource dictionary
        self.offsets[2] = len(self.buffer)
        self._out('2 0 obj')
        self._out('<<')
        self._putresourcedict()
        self._out('>>')
        self._out('endobj')
        if self.files:
            self._putfiles()

        if self.encrypted:
            self._newobj()
            self.enc_obj_id = self.n
            self._out('<<')
            self._putencription()
            self._out('>>')
            self._out('endobj')

    def _putinfo(self):
        self._out('/Producer ' + self._textstring('PyFPDF ' + FPDF_VERSION + ' https://code.google.com/p/ttfpdf/'))
        if hasattr(self, 'title'):
            self._out('/Title ' + self._textstring(self.title))
        if hasattr(self, 'subject'):
            self._out('/Subject ' + self._textstring(self.subject))
        if hasattr(self, 'author'):
            self._out('/Author ' + self._textstring(self.author))
        if hasattr (self, 'keywords'):
            self._out('/Keywords ' + self._textstring(self.keywords))
        if hasattr(self, 'creator'):
            self._out('/Creator ' + self._textstring(self.creator))
        self._out('/CreationDate ' + self._textstring('D:' + datetime.now().strftime('%Y%m%d%H%M%S')))

    def _putcatalog(self):
        self._out('/Type /Catalog')
        self._out('/Pages 1 0 R')
        if self.zoom_mode == 'fullpage':
            self._out('/OpenAction [3 0 R /Fit]')
        elif self.zoom_mode == 'fullwidth':
            self._out('/OpenAction [3 0 R /FitH null]')
        elif self.zoom_mode == 'real':
            self._out('/OpenAction [3 0 R /XYZ null null 1]')
        elif not isinstance(self.zoom_mode, basestring):
            self._out('/OpenAction [3 0 R /XYZ null null ' + str(self.zoom_mode / 100) + ']')
        if self.layout_mode == 'single':
            self._out('/PageLayout /SinglePage')
        elif self.layout_mode == 'continuous':
            self._out('/PageLayout /OneColumn')
        elif self.layout_mode == 'two':
            self._out('/PageLayout /TwoColumnLeft')

        if self.files:
            self._out('/Names <</EmbeddedFiles ' + str(self.n_files) + ' 0 R>>')

    def _putheader(self):
        self._out('%PDF-' + self.pdf_version)

    def _puttrailer(self):
        self._out('/Size ' + str(self.n+1))
        self._out('/Root ' + str(self.n) + ' 0 R')
        self._out('/Info ' + str(self.n-1) + ' 0 R')
        if self.encrypted:
            self._out('/Encrypt ' + str(self.enc_obj_id) + ' 0 R')
            self._out('/ID [()()]')

    def _putencription(self):
        self._out('/Filter /Standard')
        self._out('/V 1')
        self._out('/R 2')
        self._out('/O (' + self._escape(self.o_value) + ')')
        self._out('/U (' + self._escape(self.u_value) + ')')
        self._out('/P ' + str(self.p_value))

    def _putfiles(self):
        s = ''
        for i,info in enumerate(self.files):
            file = info['file']
            name = info['name']
            desc = info['desc']
            if hasattr(file, 'seek') and callable(getattr(file, 'seek')):
                file.seek(0)
            fc = file.read()

            self._newobj()
            s += '(' + self._escape(sprintf('%03d', i)) + ') ' + str(self.n) + ' 0 R '
            self._out('<<')
            self._out('/Type /Filespec')
            self._out('/F ' + self._textstring(name) + '')
            self._out('/EF <</F ' + str(self.n+1) + ' 0 R>>')
            if desc:
                self._out('/Desc ' + self._textstring(desc))
            self._out('>>')
            self._out('endobj')

            self._newobj()
            self._out('<<')
            self._out('/Type /EmbeddedFile')
            if self.compress:
                fc = zlib.compress(fc, 9)
                self._out('/Filter /FlateDecode')
            self._out('/Length ' + str(len(fc)))
            self._out('>>')
            self._putstream(fc)
            self._out('endobj')

        self._newobj()
        self.n_files = self.n
        self._out('<<')
        self._out('/Names [' + s + ']')
        self._out('>>')
        self._out('endobj')

    def _enddoc(self):
        self._putheader()
        self._putpages()
        self._putresources()
        #Info
        self._newobj()
        self._out('<<')
        self._putinfo()
        self._out('>>')
        self._out('endobj')
        #Catalog
        self._newobj()
        self._out('<<')
        self._putcatalog()
        self._out('>>')
        self._out('endobj')
        #Cross-ref
        o = len(self.buffer)
        self._out('xref')
        self._out('0 ' + (str(self.n+1)))
        self._out('0000000000 65535 f ')
        for i in xrange(1, self.n+1):
            self._out(sprintf('%010d 00000 n ', self.offsets[i]))
        #Trailer
        self._out('trailer')
        self._out('<<')
        self._puttrailer()
        self._out('>>')
        self._out('startxref')
        self._out(o)
        self._out('%%EOF')
        self.state=3

    def _generateencryptionkey(self, user_pass, owner_pass, protection):
        """Compute encryption key"""
        user_pass = substr(user_pass + self.padding, 0, 32)
        owner_pass = substr(owner_pass + self.padding, 0, 32)
        #Compute O value
        self.o_value = self._ovalue(user_pass, owner_pass)
        #Compute encyption key
        tmp = self._md5_16(user_pass + self.o_value + chr(protection) + "\xFF\xFF\xFF")

        self.encryption_key = substr(tmp, 0, 5)
        #Compute U value
        self.u_value = self._uvalue()
        #Compute P value
        self.p_value = -((protection^255)+1)

    def _ovalue(self, user_pass, owner_pass):
        """Compute O value"""
        tmp = self._md5_16(owner_pass)
        owner_rc4_key = substr(tmp, 0, 5)
        return self._rc4(owner_rc4_key, user_pass)

    def _md5_16(self, string):
        """Get MD5 as binary string"""
        crypt = hashlib.md5(string).hexdigest()
        return crypt.decode('hex')

    def _uvalue(self):
        """Compute U value"""
        return self._rc4(self.encryption_key, self.padding)

    def _rc4(self, key, text):
        """RC4 is the standard encryption algorithm used in PDF format"""
        if self.last_rc4_key != key:
            k = key * (256/len(key) + 1)
            rc4 = range(0, 255 + 1)
            j = 0
            for i in xrange(256):
                t = rc4[i]
                j = (j + t + ord(k[i])) % 256
                rc4[i] = rc4[j]
                rc4[j] = t
            self.last_rc4_key = key
            self.last_rc4_key_c = rc4
        else:
            rc4 = self.last_rc4_key_c
        l = len(text)
        a = 0
        b = 0
        out = []
        add = out.append
        for i in xrange(l):
            a = (a + 1) % 256
            t = rc4[a]
            b = (b + t) % 256
            rc4[a] = rc4[b]
            rc4[b] = t
            k = rc4[(rc4[a] + rc4[b]) % 256]
            c = ord(text[i])^k
            add(chr(c))
        return ''.join(out)

    def _objectkey(self, n):
        """Compute key depending on object number where the encrypted data is stored"""
        return substr(self._md5_16(self.encryption_key + struct.pack('<Lx', n)), 0, 10)

    def _arc(self, x1, y1, x2, y2, x3, y3):
        h = self.h
        k = self.k
        self._out(sprintf('%.2f %.2f %.2f %.2f %.2f %.2f c ', x1*k, (h-y1)*k, x2*k, (h-y2)*k, x3*k, (h-y3)*k))

    def _transform(self, tm):
        self._out(sprintf('%.3f %.3f %.3f %.3f %.3f %.3f cm', tm[0], tm[1], tm[2], tm[3], tm[4], tm[5]))

    def _clip(self, x, y, w ,h):
        """save current Graphic State"""
        s = 'q'
        #set clipping area
        s += sprintf(' %.2f %.2f %.2f %.2f re W n', x*self.k, (self.h-y)*self.k, w*self.k, -h*self.k)
        #set up transformation matrix for gradient
        s += sprintf(' %.3f 0 0 %.3f %.3f %.3f cm', w*self.k, h*self.k, x*self.k, (self.h-(y+h))*self.k)
        self._out(s)

    def _gradient(self, type, col1, col2, coords):
        n = len(self.gradients)
        self.gradients.append({'type': type})
        if len(col1) < 3:
            col1 = [col1[0], col1[0], col1[0]]
        self.gradients[n]['col1'] = sprintf('%.3f %.3f %.3f',(col1[0]/255.0), (col1[1]/255.0), (col1[2]/255.0))
        if len(col2) < 3:
            col2 = [col2[0], col2[0], col2[0]]
        self.gradients[n]['col2'] = sprintf('%.3f %.3f %.3f',(col2[0]/255.0), (col2[1]/255.0), (col2[2]/255.0))
        self.gradients[n]['coords'] = coords
        #paint the gradient
        self._out('/Sh' + str(n) + ' sh')
        #restore previous Graphic State
        self._out('Q')

    def _putshaders(self):
        for id, grad in enumerate(self.gradients):
            if grad['type'] == 2 or grad['type'] == 3:
                self._newobj()
                self._out('<<')
                self._out('/FunctionType 2')
                self._out('/Domain [0.0 1.0]')
                self._out('/C0 [' + grad['col1'] + ']')
                self._out('/C1 [' + grad['col2'] + ']')
                self._out('/N 1')
                self._out('>>')
                self._out('endobj')
                f1 = self.n

            self._newobj()
            self._out('<<')
            self._out('/ShadingType ' + str(grad['type']))
            self._out('/ColorSpace /DeviceRGB')
            if grad['type'] == 2:
                self._out(sprintf('/Coords [%.3f %.3f %.3f %.3f]', grad['coords'][0], grad['coords'][1],
                    grad['coords'][2], grad['coords'][3]))
                self._out('/Function ' + str(f1) + ' 0 R')
                self._out('/Extend [true true] ')
                self._out('>>')
            elif grad['type'] == 3:
                #x0, y0, r0, x1, y1, r1
                #at this time radius of inner circle is 0
                self._out(sprintf('/Coords [%.3f %.3f 0 %.3f %.3f %.3f]', grad['coords'][0], grad['coords'][1],
                    grad['coords'][2], grad['coords'][3], grad['coords'][4]))
                self._out('/Function ' + str(f1) + ' 0 R')
                self._out('/Extend [true true] ')
                self._out('>>')
            elif grad['type'] == 6:
                self._out('/BitsPerCoordinate 16')
                self._out('/BitsPerComponent 8')
                self._out('/Decode[0 1 0 1 0 1 0 1 0 1]')
                self._out('/BitsPerFlag 8')
                self._out('/Length ' + str(len(grad['stream'])))
                self._out('>>')
                self._putstream(grad['stream'])
            self._out('endobj')
            self.gradients[id]['id'] = self.n

    def _point(self, x, y):
        """Sets a draw point"""
        self._out(sprintf('%.2f %.2f m', x * self.k, (self.h - y) * self.k))

    def _line(self, x, y):
        """Draws a line from last draw point"""
        self._out(sprintf('%.2f %.2f l', x * self.k, (self.h - y) * self.k))

    def _curve(self, x1, y1, x2, y2, x3, y3):
        """Draws a Bezier curve from last draw point"""
        self._out(sprintf('%.2f %.2f %.2f %.2f %.2f %.2f c', x1 * self.k, (self.h - y1) * self.k, x2 * self.k,
            (self.h - y2) * self.k, x3 * self.k, (self.h - y3) * self.k))

    def _cell_fit(self, w, h=0, txt='', border=0, ln=0, allign='', fill=False, link='', scale=False, force=True):
        """Cell with horizontal scaling if text is too wide"""
        #Get string width
        str_width = self.get_string_width(txt)
        #        if self.unifont_subset:
        #            str_width /= 11.0
        #Calculate ratio to fit cell
        if w == 0:
            w = self.w - self.r_margin - self.x
        ratio = (w - self.c_margin * 2.0) / str_width
        fit = (ratio < 1 or (ratio > 1 and force))
        if fit:
            if scale:
                #Calculate horizontal scaling
                horiz_scale = ratio * 100.0
                #Set horizontal scaling
                self._out(sprintf('BT %.2F Tz ET',horiz_scale))
            else:
                #Calculate character spacing in points
                char_space = (w - self.c_margin * 2.0 - str_width) / max(mb_strlen(txt) - 1, 1) * self.k
                #Set character spacing
                self._out(sprintf('BT %.2F Tc ET',char_space))
                #Override user alignment (since text will fill up cell)
            allign = ''
            #Pass on to Cell method
        self.cell(w, h, txt, border, ln, allign, fill, link)
        #Reset character spacing/horizontal scaling
        if fit:
            self._out('BT ' + ('100 Tz' if scale else '0 Tc') + ' ET')
#End of class


if __name__ == "__main__":
    pdf = TTFPDF()
    pdf.add_page()
#    pdf.set_protection((),'1', '2')

    pdf.add_font('DejaVu','', 'DejaVuSans.ttf', True)
#    pdf.add_font('Courier','', 'courier.py')
    pdf.set_font('DejaVu','U',14)

    txt = open('HelloWorld.txt', 'r')
    txt.seek(3)
    t = txt.read()
    pdf.cell_fit_space_force(80, 4, t, 1)
    pdf.text_with_direction(30,80,t, 'D')
    pdf.text_with_rotation(50,60,t,45,13)
#    pdf.cell_fit_scale(30, 10, 'This text is short enough.',1,1)
    txt.close()
#    pdf.rounded_rectangle(10,12,40,40,10,'', '13')
#    pdf.shadow_cell(10, 10, 'bcd')

    from cStringIO import StringIO
    a = StringIO()
    a.write('some text')
    pdf.attach(a, name='a.txt')


#    pdf.set_draw_color(120)
#    pdf.rect(50, 20, 40, 10, 'D')
#    pdf.set_xy(50, 20)
#    pdf.set_draw_color(0)
#
#    pdf.start_transform()
#    pdf.scale_xy(150, 50, 30)
#    pdf.translate(7, 5)
#    pdf.rotate(20, 50, 60)
#    pdf.skew_y(-30, 50, 20)
#    pdf.mirror_l(-20, 60, 60)
#    pdf.mirror_p()
#    pdf.rect(50, 20, 40, 10, 'D')
#    pdf.stop_transform()

#    pdf.linear_gradient(10, 90, 50, 50, (255,0,0), (0,0,200), (0,1,0, 0))
#    pdf.radial_gradient(110, 90, 50, 50, [255], [0],)
#    pdf.coons_patch_mesh(10, 145, 50, 50, (255, 255, 0), (0,0,200), (0,255,0), (255,0,0))

#    style = {'width': 0.5, 'cap': 'butt', 'join': 'miter', 'dash': '1,1', 'phase': 10, 'color': (0, 0, 0)}
#    pdf.styled_line(5, 10, 80, 30, style)
#    pdf.styled_rect(145, 10, 40, 20, 'D', {'all': style})
#    pdf.styled_curve(140, 40, 150, 55, 180, 45, 200, 75, 'DF', style, (200, 220, 200))
#    pdf.styled_ellipse(100, 105, 20, 10, 0, 0, 360, '', style)
#    pdf.styled_circle(25, 105, 10, 0, 360, '', style)
#    pdf.styled_polygon([160,135,190,155,170,155,200,160,160,165], 'DF', {'all': style}, (220, 220, 220))
#    pdf.styled_regular_polygon(160, 190, 15, 10)
#    pdf.styled_star_polygon(160, 230, 15, 10, 3)
#    pdf.styled_rounded_rect(95, 255, 40, 30, 10.0, '1111', '', style)

#    pdf.code128(50,20,'CODE 128',80,20)
#    pdf.code128(50,70,'Code 128',80,20)
#    pdf.code128(50,120,'12345678901234567890',110,20)
    pdf.code128(50,170,'1',125,20)

    pdf.output('doc.pdf', dest='F')