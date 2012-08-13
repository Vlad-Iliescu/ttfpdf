#!/usr/bin/env python
# -*- coding: latin-1 -*-
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

#    def rotate(self, angle, x=None, y=None):
#        if x is None:
#            x = self.x
#        if y is None:
#            y = self.y;
#        if self.angle!=0:
#            self._out('Q')
#        self.angle = angle
#        if angle!=0:
#            angle *= math.pi/180;
#            c = math.cos(angle);
#            s = math.sin(angle);
#            cx = x*self.k;
#            cy = (self.h-y)*self.k
#            s = sprintf('q %.5F %.5F %.5F %.5F %.2F %.2F cm 1 0 0 1 %.2F %.2F cm',c,s,-s,c,cx,cy,-cx,-cy)
#            self._out(s)

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
                if len(subset):
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

    def _putresources(self):
        self._putfonts()
        self._putimages()
        #Resource dictionary
        self.offsets[2] = len(self.buffer)
        self._out('2 0 obj')
        self._out('<<')
        self._putresourcedict()
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

    def _putheader(self):
        self._out('%PDF-' + self.pdf_version)

    def _puttrailer(self):
        self._out('/Size ' + str(self.n+1))
        self._out('/Root ' + str(self.n) + ' 0 R')
        self._out('/Info ' + str(self.n-1) + ' 0 R')

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

    def interleaved2of5(self, txt, x, y, w=1.0, h=10.0):
        """Barcode I2of5 (numeric), adds a 0 if odd lenght"""
        narrow = w / 3.0
        wide = w

        # wide/narrow codes for the digits
        bar_char={}
        bar_char['0'] = 'nnwwn'
        bar_char['1'] = 'wnnnw'
        bar_char['2'] = 'nwnnw'
        bar_char['3'] = 'wwnnn'
        bar_char['4'] = 'nnwnw'
        bar_char['5'] = 'wnwnn'
        bar_char['6'] = 'nwwnn'
        bar_char['7'] = 'nnnww'
        bar_char['8'] = 'wnnwn'
        bar_char['9'] = 'nwnwn'
        bar_char['A'] = 'nn'
        bar_char['Z'] = 'wn'

        self.set_fill_color(0)
        code = txt
        # add leading zero if code-length is odd
        if len(code) % 2 != 0:
            code = '0' + code

        # add start and stop codes
        code = 'AA' + code.lower() + 'ZA'

        for i in xrange(0, len(code), 2):
            # choose next pair of digits
            char_bar = code[i]
            char_space = code[i+1]
            # check whether it is a valid digit
            if not char_bar in bar_char.keys():
                raise RuntimeError ('Invalid character for barcode I25: %s' % char_bar)
            if not char_space in bar_char.keys():
                raise RuntimeError ('Invalid character for barcode I25: %s' % char_space)

            # create a wide/narrow-sequence (first digit=bars, second digit=spaces)
            seq = ''
            for s in xrange(0, len(bar_char[char_bar])):
                seq += bar_char[char_bar][s] + bar_char[char_space][s]

            for bar in xrange(0, len(seq)):
                # set line_width depending on value
                if seq[bar] == 'n':
                    line_width = narrow
                else:
                    line_width = wide

                # draw every second value, because the second digit of the pair is represented by the spaces
                if bar % 2 == 0:
                    self.rect(x, y, line_width, h, 'F')

                x += line_width

    def code39(self, txt, x, y, w=1.5, h=5.0):
        """Barcode 3of9"""
        wide = w
        narrow = w /3.0
        gap = narrow

        bar_char={}
        bar_char['0'] = 'nnnwwnwnn'
        bar_char['1'] = 'wnnwnnnnw'
        bar_char['2'] = 'nnwwnnnnw'
        bar_char['3'] = 'wnwwnnnnn'
        bar_char['4'] = 'nnnwwnnnw'
        bar_char['5'] = 'wnnwwnnnn'
        bar_char['6'] = 'nnwwwnnnn'
        bar_char['7'] = 'nnnwnnwnw'
        bar_char['8'] = 'wnnwnnwnn'
        bar_char['9'] = 'nnwwnnwnn'
        bar_char['A'] = 'wnnnnwnnw'
        bar_char['B'] = 'nnwnnwnnw'
        bar_char['C'] = 'wnwnnwnnn'
        bar_char['D'] = 'nnnnwwnnw'
        bar_char['E'] = 'wnnnwwnnn'
        bar_char['F'] = 'nnwnwwnnn'
        bar_char['G'] = 'nnnnnwwnw'
        bar_char['H'] = 'wnnnnwwnn'
        bar_char['I'] = 'nnwnnwwnn'
        bar_char['J'] = 'nnnnwwwnn'
        bar_char['K'] = 'wnnnnnnww'
        bar_char['L'] = 'nnwnnnnww'
        bar_char['M'] = 'wnwnnnnwn'
        bar_char['N'] = 'nnnnwnnww'
        bar_char['O'] = 'wnnnwnnwn'
        bar_char['P'] = 'nnwnwnnwn'
        bar_char['Q'] = 'nnnnnnwww'
        bar_char['R'] = 'wnnnnnwwn'
        bar_char['S'] = 'nnwnnnwwn'
        bar_char['T'] = 'nnnnwnwwn'
        bar_char['U'] = 'wwnnnnnnw'
        bar_char['V'] = 'nwwnnnnnw'
        bar_char['W'] = 'wwwnnnnnn'
        bar_char['X'] = 'nwnnwnnnw'
        bar_char['Y'] = 'wwnnwnnnn'
        bar_char['Z'] = 'nwwnwnnnn'
        bar_char['-'] = 'nwnnnnwnw'
        bar_char['.'] = 'wwnnnnwnn'
        bar_char[' '] = 'nwwnnnwnn'
        bar_char['*'] = 'nwnnwnwnn'
        bar_char['$'] = 'nwnwnwnnn'
        bar_char['/'] = 'nwnwnnnwn'
        bar_char['+'] = 'nwnnnwnwn'
        bar_char['%'] = 'nnnwnwnwn'

        self.set_fill_color(0)
        code = txt

        code = code.upper()
        for i in xrange (0, len(code), 2):
            char_bar = code[i]

            if not char_bar in bar_char.keys():
                raise RuntimeError ('Invalid character for the barcode: %s' % char_bar)

            seq = ''
            for s in xrange(0, len(bar_char[char_bar])):
                seq += bar_char[char_bar][s]

            for bar in xrange(0, len(seq)):
                if seq[bar] == 'n':
                    line_width = narrow
                else:
                    line_width = wide

                if bar % 2 == 0:
                    self.rect(x,y,line_width,h,'F')
                x += line_width
        x += gap

#End of class


if __name__ == "__main__":
    pdf = TTFPDF()
    pdf.add_page()

    pdf.add_font('DejaVu','', 'DejaVuSans.ttf', True)
    pdf.set_font('DejaVu','',14)

    txt = open('HelloWorld.txt', 'r')
    pdf.write(8, txt.read())
    txt.close()

    pdf.output('doc.pdf')