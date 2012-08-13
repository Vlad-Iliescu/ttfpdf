__author__ = 'Vlad'

#/*******************************************************************************
#* TTFontFile class                                                             *
#*                                                                              *
#* This class is based on The ReportLab Open Source PDF library                 *
#* written in Python - http://www.reportlab.com/software/opensource/            *
#* together with ideas from the OpenOffice source code and others.              *
#*                                                                              *
#* Version:  1.04                                                               *
#* Date:     2011-09-18                                                         *
#* Author:   Ian Back <ianb@bpm1.com>                                           *
#* License:  LGPL                                                               *
#* Copyright (c) Ian Back, 2010                                                 *
#* This header must be retained in any redistribution or                        *
#* modification of the file.                                                    *
#*                                                                              *
#*******************************************************************************/
#
#// Define the value used in the "head" table of a created TTF file
#// 0x74727565 "true" for Mac
#// 0x00010000 for Windows
#// Either seems to work for a font embedded in a PDF file
#// when read by Adobe Reader on a Windows PC(!)

_TTF_MAC_HEADER = False
#TrueType Font Glyph operators
GF_WORDS = (1 << 0)
GF_SCALE = (1 << 3)
GF_MORE = (1 << 5)
GF_XYSCALE = (1 << 6)
GF_TWOBYTWO = (1 << 7)

from struct import pack, unpack
import re

class TTFontFile:
    def __init__(self):
        #Maximum size of glyf table to read in as string (otherwise reads each glyph from file)
        self.max_str_len_read = 200000

    def get_metrics(self, file):
        self.filename = file
        self.fh = open(file,'rb')
        self._pos = 0
        self.char_widths = ''
        self.glyph_pos = []
        self.char_to_glyph = {}
        self.tables = {}
        self.otables = {}
        self.ascent = 0
        self.descent = 0
        self.TTC_fonts = {}
        self.version = version = self.read_ulong()
        if version == 0x4F54544F:
            raise RuntimeError('Postscript outlines are not supported')
        if version == 0x74746366:
            raise RuntimeError('TrueType Fonts Collections not supported')
        if version not in (0x00010000,0x74727565):
            raise RuntimeError('Not a TrueType font: version = {0}'.format(version))
        self.read_table_directory()
        self.extract_info()
        self.fh.close()

    def read_table_directory(self):
        self.num_tables = self.read_ushort()
        self.search_range = self.read_ushort()
        self.entry_selector = self.read_ushort()
        self.range_shift = self.read_ushort()
        self.tables = {}
        for i in xrange(self.num_tables):
            record = {}
            record['tag'] = self.read_tag()
            record['checksum'] = (self.read_ushort(), self.read_ushort())
            record['offset'] = self.read_ulong()
            record['length'] = self.read_ulong()
            self.tables[record['tag']] = record

    def sub32(self, x, y):
        xlo = x[1]
        xhi = x[0]
        ylo = y[1]
        yhi = y[0]
        if ylo > xlo:
            xlo += 1 << 16
            yhi += 1
        reslo = xlo - ylo
        if yhi > xhi:
            xhi += 1 << 16
        reshi = xhi - yhi
        reshi &= 0xFFFF
        return reshi, reslo

    def calcChecksum(self, data):
        if len(data) % 4:
            data += "\0"*(4-(len(data) % 4))
        hi = 0x0000
        lo = 0x0000
        for i in xrange(0,len(data),4):
            hi = (ord(data[i])<<8) + ord(data[i+1])
            lo = (ord(data[i+2])<<8) + ord(data[i+3])
            hi += lo >> 16
            lo &= 0xFFFF
            hi &= 0xFFFF
        return hi, lo

    def get_table_pos(self, tag):
        offset = self.tables[tag]['offset']
        length = self.tables[tag]['length']
        return offset, length

    def seek(self, pos):
        self._pos = pos
        self.fh.seek(self._pos)

    def skip(self, delta):
        self._pos = self._pos + delta
        self.fh.seek(self._pos)

    def seek_table(self, tag, offset_in_table = 0):
        tpos = self.get_table_pos(tag)
        self._pos = tpos[0] + offset_in_table
        self.fh.seek(self._pos)
        return self._pos

    def read_tag(self):
        self._pos += 4
        return self.fh.read(4)

    def read_short(self):
        self._pos += 2
        s = self.fh.read(2)
        a = (ord(s[0])<<8) + ord(s[1])
        if a & (1 << 15):
            a = (a - (1 << 16))
        return a

    def unpack_short(self, s):
        a = (ord(s[0])<<8) + ord(s[1])
        if a & (1 << 15):
            a = (a - (1 << 16))
        return a

    def read_ushort(self):
        self._pos += 2
        s = self.fh.read(2)
        return (ord(s[0]) << 8) + ord(s[1])

    def read_ulong(self):
        self._pos += 4
        s = self.fh.read(4)
        return (ord(s[0]) * 16777216) + (ord(s[1]) << 16) + (ord(s[2]) << 8) + ord(s[3]) #16777216  = 1<<24

    def get_ushort(self, pos):
        self.fh.seek(pos)
        s = self.fh.read(2)
        return (ord(s[0]) << 8) + ord(s[1])

    def get_ulong(self, pos):
        self.fh.seek(pos)
        s = self.fh.read(4)
        return (ord(s[0]) * 16777216) + (ord(s[1]) << 16) + (ord(s[2]) << 8) + ord(s[3]) #16777216  = 1<<24

    def pack_short(self, val):
        if val < 0:
            val = abs(val)
            val = ~val
            val += 1
        return pack(">H", val)

    def splice(self, stream, offset, value):
        return stream[:offset] + value + stream[offset+len(value):]

    def _set_ushort(self, stream, offset, value):
        up = pack(">H", value)
        return self.splice(stream, offset, up)

    def _set_short(self, stream, offset, val):
        if val < 0:
            val = abs(val)
            val = ~val
            val += 1
        up = pack(">H", val)
        return self.splice(stream, offset, up)

    def get_chunk(self, pos, length):
        self.fh.seek(pos)
        if length < 1:
            return ''
        return self.fh.read(length)

    def get_table(self, tag):
        pos, length = self.get_table_pos(tag)
        if not length:
            raise RuntimeError('Truetype font ({0}): error reading table: {1}'.format(self.filename, tag))
        self.fh.seek(pos)
        return self.fh.read(length)

    def add(self, tag, data):
        if tag == 'head':
            data = self.splice(data,8,"\0\0\0\0")
        self.otables[tag] = data

########################################################################################################################
########################################################################################################################

########################################################################################################################

    def extract_info(self):
#        ///////////////////////////////////
#        // name - Naming table
#        ///////////////////////////////////
        self.s_family_class = 0
        self.s_family_sub_class = 0
        name_offset = self.seek_table("name")
        format = self.read_ushort()
        if format != 0:
            raise RuntimeError('Unknown name table format {0}'.format(format))
        num_records = self.read_ushort()
        string_data_offset = name_offset + self.read_ushort()
        names = {1:'', 2:'', 3:'', 4:'',6:''}
        k = names.keys()
        name_count = len(names)
        for i in xrange(num_records):
            platform_id = self.read_ushort()
            encoding_id = self.read_ushort()
            languageId = self.read_ushort()
            nameId = self.read_ushort()
            length = self.read_ushort()
            offset = self.read_ushort()
            if nameId not in k:
                continue
            n = ''
            if platform_id == 3 and encoding_id == 1 and languageId == 0x409:
                #Microsoft, Unicode, US English, PS Name
                opos = self._pos
                self.seek(string_data_offset + offset)
                if length % 2:
                    raise RuntimeError("PostScript name is UTF-16BE string of odd length")
                length /= 2
                n_l = []
                n_a = n_l.append
                while length > 0:
                    char = self.read_ushort()
                    n_a(chr(char))
                    length -= 1
                n = ''.join(n_l)
                self._pos = opos
                self.seek(opos)
            elif platform_id == 1 and encoding_id == 0 and languageId == 0:
                #Macintosh, Roman, English, PS Name
                opos = self._pos
                n = self.get_chunk(string_data_offset + offset,length)
                self._pos = opos
                self.seek(opos)

            if n and names[nameId] == '':
                names[nameId] = n
                name_count -= 1
                if not name_count:
                    break

        if names[6]:
            ps_name = names[6]
        elif names[4]:
            ps_name = re.sub(' ', '-', names[4])
        elif names[1]:
            ps_name = re.sub(' ' ,'-', names[1])
        else:
            ps_name = ''

        if not ps_name:
            raise RuntimeError("Could not find PostScript font name")
        self.name = ps_name
        self.family_name = names[1] if names[1] else ps_name
        self.style_name = names[2] if names[2] else 'Regular'
        self.full_name = names[4] if names[4] else ps_name
        self.unique_font_id = names[3] if names[3] else ps_name
        if names[6]:
            self.full_name = names[6]

#        ///////////////////////////////////
#        // head - Font header table
#        ///////////////////////////////////

        self.seek_table("head")
        self.skip(18)
        self.units_per_em = units_per_em = self.read_ushort()
        scale = 1000.0 / units_per_em
        self.skip(16)
        x_min = self.read_ushort()
        y_min = self.read_ushort()
        x_max = self.read_ushort()
        y_max = self.read_ushort()
        self.bbox = (x_min*scale, y_min*scale, x_max*scale, y_max*scale)
        self.skip(3*2)
        index_to_loc_format = self.read_ushort()
        glyph_data_format = self.read_ushort()
        if glyph_data_format:
            raise RuntimeError('Unknown glyph data format {0}'.format(glyph_data_format))

#        ///////////////////////////////////
#        // hhea metrics table
#        ///////////////////////////////////
#        // ttf2t1 seems to use this value rather than the one in OS/2 - so put in for compatibility

        if 'hhea' in self.tables:
            self.seek_table('hhea')
            self.skip(4)
            hhea_ascender = self.read_ushort()
            hhea_descender = self.read_ushort()
            self.ascent = hhea_ascender * scale
            self.descent = hhea_descender * scale

#        ///////////////////////////////////
#        // OS/2 - OS/2 and Windows metrics table
#        ///////////////////////////////////

        if 'OS/2' in self.tables:
            self.seek_table('OS/2')
            version = self.read_ushort()
            self.skip(2)
            us_weight_class = self.read_ushort()
            self.skip(2)
            fs_type = self.read_ushort()
            if fs_type == 0x0002 or (fs_type & 0x0300):
                self.restricted_use = True
                raise RuntimeError('ERROR - Font file {0} cannot be embedded ' \
                                   'due to copyright restrictions.'.format(self.filename))
            self.skip(20)
            sf = self.read_ushort()
            self.s_family_class = (sf >> 8)
            self.s_family_sub_class = (sf &0xFF)
            self._pos += 10 #PANOSE = 10 byte length
            panose = self.fh.read(10)
            self.skip(26)
            s_typo_ascender = self.read_ushort()
            s_typo_descender = self.read_ushort()
            if not(hasattr(self,'ascent') and self.ascent):
                self.ascent = s_typo_ascender * scale
            if not(hasattr(self,'descent') and self.descent):
                self.descent = s_typo_descender * scale
            if version > 1:
                self.skip(16)
                s_cap_height = self.read_ushort()
                self.cap_height = s_cap_height * scale
            else:
                self.cap_height = self.ascent
        else:
            us_weight_class = 500
            if not(hasattr(self,'ascent') and self.ascent):
                self.ascent = y_max * scale
            if not(hasattr(self,'descent') and self.descent):
                self.descent = y_min * scale
            self.cap_height = self.ascent
        self.stem_v = 50 + int((us_weight_class / 65.0)**2)

#        ///////////////////////////////////
#        // post - PostScript table
#        ///////////////////////////////////
        self.seek_table('post')
        self.skip(4)
        self.italic_angle = self.read_short() + self.read_ushort() / 65536.0
        self.underline_position = self.read_short() * scale
        self.underline_thickness = self.read_short() * scale
        is_fixed_pitch = self.read_ulong()

        self.flags = 4

        if self.italic_angle:
            self.flags |= 64
        if us_weight_class >= 600:
            self.flags |= 262144
        if is_fixed_pitch:
            self.flags |= 1

#        ///////////////////////////////////
#        // hhea - Horizontal header table
#        ///////////////////////////////////
        self.seek_table('hhea')
        self.skip(32)
        metric_data_format = self.read_short()
        if metric_data_format:
            raise RuntimeError('Unknown horizontal metric data format {0}'.format(metric_data_format))
        number_of_h_metrics = self.read_ushort()
        if not number_of_h_metrics:
            raise RuntimeError('Number of horizontal metrics is 0')

#        ///////////////////////////////////
#        // maxp - Maximum profile table
#        ///////////////////////////////////
        self.seek_table('maxp')
        self.skip(4)
        num_glyphs = self.read_ushort()

#        ///////////////////////////////////
#        // cmap - Character to glyph index mapping table
#        ///////////////////////////////////
        cmap_offset = self.seek_table('cmap')
        self.skip(2)
        cmap_table_count = self.read_ushort()
        unicode_cmap_offset = 0
        for i in xrange(cmap_table_count):
            platform_id = self.read_ushort()
            encoding_id = self.read_ushort()
            offset = self.read_ulong()
            save_pos = self._pos
            if (platform_id == 3 and encoding_id == 1) or platform_id == 0:
                #Microsoft, Unicode
                format = self.get_ushort(cmap_offset + offset)
                if format == 4:
                    if not unicode_cmap_offset:
                        unicode_cmap_offset = cmap_offset + offset
                    break
            self.seek(save_pos)
        if not unicode_cmap_offset:
            raise RuntimeError('Font ({0}) does not have cmap for Unicode ' \
                               '(platform 3, encoding 1, format 4, or platform 0, ' \
                               'any encoding, format 4)'.format(self.filename))
        glyph_to_char = {}
        char_to_glyph = {}
        self.get_CMAP4(unicode_cmap_offset, glyph_to_char, char_to_glyph)

#        ///////////////////////////////////
#        // hmtx - Horizontal metrics table
#        ///////////////////////////////////
        self.get_HMTX(number_of_h_metrics, num_glyphs, glyph_to_char, scale)

########################################################################################################################
########################################################################################################################

    def make_subset(self, file, subset):
        self.filename = file
        self.fh = open(file, 'rb')
        self._pos = 0
        self.char_widths = ''
        self.glyph_pos = []
        self.char_to_glyph = {}
        self.tables = {}
        self.otables = {}
        self.ascent = 0
        self.descent = 0
        self.skip(4)
        self.max_uni = 0
        self.read_table_directory()

#        ///////////////////////////////////
#        // head - Font header table
#        ///////////////////////////////////
        self.seek_table('head')
        self.skip(50)
        index_to_loc_format = self.read_ushort()
        glyph_data_format = self.read_ushort()

#        ///////////////////////////////////
#        // hhea - Horizontal header table
#        ///////////////////////////////////

        self.seek_table('hhea')
        self.skip(32)
        metric_data_format = self.read_ushort()
        orign_h_metrics = number_of_h_metrics = self.read_ushort()

#        ///////////////////////////////////
#        // maxp - Maximum profile table
#        ///////////////////////////////////
        self.seek_table('maxp')
        self.skip(4)
        num_glyphs = self.read_ushort()

#        ///////////////////////////////////
#        // cmap - Character to glyph index mapping table
#        ///////////////////////////////////
        cmap_offset = self.seek_table('cmap')
        self.skip(2)
        cmap_table_count = self.read_ushort()
        unicode_cmap_offset = 0
        for i in xrange(cmap_table_count):
            platform_id = self.read_ushort()
            encoding_id = self.read_ushort()
            offset = self.read_ulong()
            save_pos = self._pos
            if (platform_id == 3 and encoding_id == 1) or platform_id == 0:
                #Microsoft, Unicode
                format = self.get_ushort(cmap_offset + offset)
                if format == 4:
                    unicode_cmap_offset = cmap_offset + offset
                    break
            self.seek(save_pos)

        if not unicode_cmap_offset:
            raise RuntimeError('Font ({0}) does not have cmap for Unicode '
                               '(platform 3, encoding 1, format 4, or platform 0, '
                               'any encoding, format 4)'.format(self.filename))
        glyph_to_char = {}
        char_to_glyph = {}
        self.get_CMAP4(unicode_cmap_offset, glyph_to_char, char_to_glyph)

        self.char_to_glyph = char_to_glyph

#        ///////////////////////////////////
#        // hmtx - Horizontal metrics table
#        ///////////////////////////////////

        scale = 1 #not used
        self.get_HMTX(number_of_h_metrics, num_glyphs, glyph_to_char, scale)

#        ///////////////////////////////////
#        // loca - Index to location
#        ///////////////////////////////////
        self.get_LOCA(index_to_loc_format, num_glyphs)

        subset_glyphs = {0:0}
        subset_char_to_glyph = {}
        for code in subset:
            if code in self.char_to_glyph:
                subset_glyphs[self.char_to_glyph[code]] = code #Old Glyph ID => Unicode
                subset_char_to_glyph[code] = self.char_to_glyph[code]
            self.max_uni = max(self.max_uni, code)

        start, dummy = self.get_table_pos('glyf')

        glyph_set = {}
        n = 0
        fs_last_char_index = 0  # maximum Unicode index (character code) in this font, according to the cmap subtable
                                # for platform ID 3 and platform- specific encoding ID 0 or 1.
        sorted_subset_glyphs = sorted(subset_glyphs)
        self.subset_glyfs_order = sorted_subset_glyphs[:]
        for original_glyph_idx in sorted_subset_glyphs:
            uni = subset_glyphs[original_glyph_idx]
            fs_last_char_index = max(fs_last_char_index, uni)
            glyph_set[original_glyph_idx] = n #old glyphID to new glyphID
            n += 1

        code_to_glyph = {}
        for uni in sorted(subset_char_to_glyph):
            original_glyph_idx = subset_char_to_glyph[uni]
            code_to_glyph[uni] = glyph_set[original_glyph_idx]

        self.code_to_glyph = code_to_glyph

        for original_glyph_idx in sorted_subset_glyphs:
#            uni = subset_glyphs[original_glyph_idx]
            self.get_glyphs(original_glyph_idx, start, glyph_set, subset_glyphs)

        num_glyphs = number_of_h_metrics = len(subset_glyphs)

        #tables copied from the original
        tags = ['name']
        for tag in tags:
            self.add(tag,self.get_table(tag))
        tags = ['cvt ', 'fpgm', 'prep', 'gasp']
        for tag in tags:
            if tag in self.tables:
                self.add(tag, self.get_table(tag))

        #post - PostScript
        opost = self.get_table('post')
        post = ''.join(["\x00\x03\x00\x00", opost[4:4+12],
                        "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"])
        self.add('post', post)

#        key_0 = sorted(code_to_glyph)[0]
#        del code_to_glyph[key_0]
        if 0 in code_to_glyph:
            del code_to_glyph[0]

        range_id = 0
        range = {}
        prev_cid = -2
        prev_gl_idx = -1
        #for each character
        for cid in sorted(code_to_glyph):
            gl_idx = code_to_glyph[cid]
            if cid == (prev_cid + 1) and gl_idx == (prev_gl_idx + 1):
                if range_id not in range:
                    range[range_id] = []
                range[range_id].append(gl_idx)
            else:
                # new range
                range_id = cid
                range[range_id] = [gl_idx]
            prev_cid = cid
            prev_gl_idx = gl_idx

        #cmap - Character to glyph mapping - Format 4 (MS / )
        seg_count = len(range) + 1 # + 1 Last segment has missing character 0xFFFF
        search_range = 1
        entry_selector = 0
        while search_range * 2 <= seg_count:
            search_range *= 2
            entry_selector += 1
        search_range *= 2
        range_shift = seg_count * 2 - search_range
        length = 16 + (8 * seg_count) + (num_glyphs + 1)
        cmap = [
            0, 1,           #Index : version, number of encoding subtables
            3, 1,           #Encoding Subtable : platform (MS=3), encoding (Unicode)
            0, 12,          #Encoding Subtable : offset (hi,lo)
            4, length, 0,   #Format 4 Mapping subtable: format, length, language
            seg_count * 2,
            search_range,
            entry_selector,
            range_shift
        ]
        add = cmap.append
        #endCode(s)
        sorted_range = sorted(range)
        for start in sorted_range:
            sub_range = range[start]
            end_code = start + (len(sub_range) - 1)
            add(end_code)   # endCode(s)
        add(0xFFFF)	#endCode of last Segment
        add(0)      #reservedPad

        #startCode(s)
        for start in sorted_range:
            add(start)
        add(0xFFFF) #startCode of last Segment

        #idDelta(s)
        for start in sorted_range:
            sub_range = range[start]
            id_delta = -(start - sub_range[0])
            n += len(sub_range)
            add(id_delta)   #idDelta(s)
        add(1)  #idDelta of last Segment

        #idRangeOffset(s)
        for start in sorted_range:
            add(0)  #idRangeOffset[segCount]  	Offset in bytes to glyph indexArray, or 0
        add(0)  #idRangeOffset of last Segment

        for start in sorted_range:
            sub_range = range[start]
            for gl_idx in sub_range:
                add(gl_idx)

        add(0)  #Mapping for last character
        cmap_list = []
        add_cm_l = cmap_list.append
        for cm in cmap:
#            add_cm_l(pack(">H" if cm>0 else ">h", cm))
            add_cm_l(pack('>H' if cm>0 else '>h', cm) if cm > -32768 else pack('>l', cm)[-2:])
        cmap_str = ''.join(cmap_list)

        self.add('cmap', cmap_str)

        #glyf - Glyph data
        glyf_offset, glyf_length = self.get_table_pos('glyf')
        if glyf_length < self.max_str_len_read:
            glyph_data = self.get_table('glyf')
#        else:
#            raise RuntimeError('Glyph length ({0}) greater then max read ({1}) in table "glyf"'.format(
#                glyf_length, self.max_str_len_read))

        offsets = []
        offsets_add = offsets.append

#        glyf = ''
        glyf_list = []
        glyf_add = glyf_list.append
        pos = 0

#        hmtx_str = ''
        hmtx_list = []
        hmtx_add = hmtx_list.append
        x_min_t = 0
        y_min_t = 0
        x_max_t = 0
        y_max_t = 0
        advance_width_max = 0
        min_left_side_bearing = 0
        min_right_side_bearing = 0
        x_max_extent = 0
        max_points = 0              #points in non-compound glyph
        max_contours = 0            #contours in non-compound glyph
        max_component_points = 0    #points in compound glyph
        max_component_contours = 0  #contours in compound glyph
        max_component_elements = 0  #number of glyphs referenced at top level
        max_component_depth = 0     #levels of recursion, set to 0 if font has only simple glyphs
        self.glyph_data = {}

        for original_glyph_idx in self.subset_glyfs_order:
            uni = subset_glyphs[original_glyph_idx]
            #hmtx - Horizontal Metrics
            hm = self.get_h_metric(orign_h_metrics, original_glyph_idx)
            hmtx_add(hm)

            offsets_add(pos)
            glyph_pos = self.glyph_pos[original_glyph_idx]
            glyph_len = self.glyph_pos[original_glyph_idx+1] - glyph_pos
            if glyf_length < self.max_str_len_read:
                data = glyph_data[glyph_pos:glyph_pos + glyph_len]
            else:
                if glyph_len > 0:
                    data = self.get_chunk(glyf_offset + glyph_pos, glyph_len)
                else:
                    data = ''
            if glyph_len > 0:
                up = unpack(">H", data[:2])

            if glyph_len > 2 and (up[0] & (1 << 15)):
                # If number of contours <= -1 i.e. composiste glyph
                pos_in_glyph = 10
                flags = GF_MORE
                n_component_elements = 0
                while flags & GF_MORE:
                    n_component_elements += 1       # number of glyphs referenced at top level
                    up = unpack(">H", data[pos_in_glyph:pos_in_glyph + 2])
                    flags = up[0]
                    up = unpack(">H", data[pos_in_glyph + 2: pos_in_glyph + 4])
                    glyph_idx = up[0]
                    if original_glyph_idx not in self.glyph_data:
                        self.glyph_data[original_glyph_idx] = {'compGlyphs': []}
                    self.glyph_data[original_glyph_idx]['compGlyphs'].append(glyph_idx)
                    data = self._set_ushort(data, pos_in_glyph + 2, glyph_set.get(glyph_idx,0)) #changed to get()
                    pos_in_glyph += 4
                    if flags & GF_WORDS:
                        pos_in_glyph += 4
                    else:
                        pos_in_glyph += 2

                    if flags & GF_SCALE:
                        pos_in_glyph += 2
                    elif flags & GF_XYSCALE:
                        pos_in_glyph += 4
                    elif flags & GF_TWOBYTWO:
                        pos_in_glyph += 8
                max_component_elements = max(max_component_elements, n_component_elements)
            glyf_add(data)
            pos += glyph_len
            if pos % 4:
                padding = 4 - (pos % 4)
                glyf_add("\0" * padding)
                pos += padding

        hmtx_str = ''.join(hmtx_list)
        glyf = ''.join(glyf_list)

        offsets_add(pos)
        self.add('glyf', glyf)

        #hmtx - Horizontal Metrics
        self.add('hmtx', hmtx_str)

        #loca - Index to location
#        loca_str = ''
        loca_list = []
        loca_add = loca_list.append
        if ((pos + 1) >> 1) > 0xFFFF:
            index_to_loc_format = 1     #long format
            for offset in offsets:
                loca_add(pack(">L", offset))
        else:
            index_to_loc_format = 0     #short format
            for offset in offsets:
                loca_add(pack(">H", offset/2))
        loca_str = ''.join(loca_list)
        self.add('loca', loca_str)

        #head - Font header
        head = self.get_table('head')
        head = self._set_ushort(head, 50, index_to_loc_format)
        self.add('head', head)

        #hhea - Horizontal Header
        hhea = self.get_table('hhea')
        hhea = self._set_ushort(hhea,34, number_of_h_metrics)
        self.add('hhea', hhea)

        #maxp - Maximum Profile
        maxp = self.get_table('maxp')
        maxp = self._set_ushort(maxp, 4, num_glyphs)
        self.add('maxp', maxp)

        #OS/2 - OS/2
        os2 = self.get_table('OS/2')
        self.add('OS/2', os2)

        self.fh.close()

        #Put the TTF file together
        stm = self.end_tt_file('')
        return stm

########################################################################################################################
#### Recursively get composite glyph data
########################################################################################################################
    def get_glyph_data(self, original_glyph_idx, max_depth, depth, points, contours):
        depth += 1
        max_depth = max(max_depth, depth)
        if len(self.glyph_data[original_glyph_idx]['compGlyphs']):
            for glyph_idx in self.glyph_data[original_glyph_idx]['compGlyphs']:
                max_depth, depth, points, contours = self.get_glyph_data(glyph_idx, max_depth, depth, points, contours)
        elif (self.glyph_data[original_glyph_idx]['nContours'] > 0) and depth > 0:
            #simple
            contours += self.glyph_data[original_glyph_idx]['nContours']
            points += self.glyph_data[original_glyph_idx]['nPoints']
        depth -= 1
        return max_depth, depth, points, contours

########################################################################################################################
#### Recursively get composite glyphs
########################################################################################################################
    def get_glyphs(self, original_glyph_idx, start, glyph_set, subset_glyphs):

#        if original_glyph_idx not in self.glyph_pos:
#            return
        glyph_pos = self.glyph_pos[original_glyph_idx]
        glyph_len = self.glyph_pos[original_glyph_idx + 1] - glyph_pos
        if not glyph_len:
            return

        self.seek(start + glyph_pos)
        number_of_contours = self.read_short()
        if number_of_contours < 0:
            self.skip(8)
            flags = GF_MORE
            while flags & GF_MORE:
                flags = self.read_ushort()
                glyph_idx = self.read_ushort()
                if glyph_idx not in glyph_set:
                    glyph_set[glyph_idx] = len(subset_glyphs) #old glyphID to new glyphID
                    subset_glyphs[glyph_idx] = 1
                    self.subset_glyfs_order.append(glyph_idx)
                save_pos = self.fh.tell()
                self.get_glyphs(glyph_idx, start, glyph_set, subset_glyphs)
                self.seek(save_pos)
                if flags & GF_WORDS:
                    self.skip(4)
                else:
                    self.skip(2)
                if flags & GF_SCALE:
                    self.skip(2)
                elif flags & GF_XYSCALE:
                    self.skip(4)
                elif flags & GF_TWOBYTWO:
                    self.skip(8)

########################################################################################################################
########################################################################################################################
    def get_HMTX(self, number_of_h_metrics, num_glyphs, glyph_to_char, scale):
        start = self.seek_table('hmtx')
        aw = 0
#        self.char_widths = ''.rjust(256*256*2, "\x00")
        char_widths = ["\x00" for _i in xrange(256*256*2)]
        n_char_widths = 0
        if number_of_h_metrics * 4 < self.max_str_len_read:
            data = self.get_chunk(start, number_of_h_metrics * 4)
            arr = unpack(">{0}H".format(len(data)/2), data)
        else:
            self.seek(start)
        for glyph in xrange(number_of_h_metrics):
            if number_of_h_metrics * 4 < self.max_str_len_read:
                aw = arr[glyph * 2]
            else:
                aw = self.read_ushort()
                lsb = self.read_ushort()
            if glyph in glyph_to_char or glyph == 0:
                if aw >= (1 << 15):
                    #1.03 Some (arabic) fonts have -ve values for width
                    #although should be unsigned value - comes out as e.g. 65108 (intended -50)
                    aw = 0
                if not glyph:
                    self.default_width = scale * aw
                    continue
                for char in glyph_to_char[glyph]:
                    if char and char != 65535:
                        w = int(round(scale * aw))
                        if not w:
                            w = 65535
                        if char  < 196608:
                            char_widths[char*2] = chr(w >> 8)
                            char_widths[char*2 +1] = chr(w & 0xFF)
                            n_char_widths += 1
        data = self.get_chunk(start + number_of_h_metrics * 4, num_glyphs * 2)
        arr = unpack(">{0}H".format(len(data)/2), data)
        diff = num_glyphs - number_of_h_metrics
        for pos in xrange(diff):
            glyph = pos + number_of_h_metrics
            if glyph in glyph_to_char:
                for char in glyph_to_char[glyph]:
                    if char and char != 65535:
                        w = int(round(scale * aw))
                        if not w:
                            w = 65535
                        if char < 196608:
                            char_widths[char * 2] = chr(w >> 8)
                            char_widths[char * 2 + 1] = chr(w & 0xFF)
                            n_char_widths += 1

        #NB 65535 is a set width of 0
        #First bytes define number of chars in font
        char_widths[0] = chr(n_char_widths >> 8)
        char_widths[1] = chr(n_char_widths & 0xFF)
        self.char_widths = ''.join(char_widths)


    def get_h_metric(self, number_of_h_metrics, gid):
        start = self.seek_table('hmtx')
        if gid < number_of_h_metrics:
            self.seek(start + gid * 4)
            hm = self.fh.read(4)
        else:
            self.seek(start + (number_of_h_metrics - 1) * 4)
            hm = self.fh.read(2)
            self.seek(start + number_of_h_metrics * 2 + gid * 2)
            hm += self.fh.read(2)
        return hm

    def get_LOCA(self, index_to_loc_format, num_glyphs):
        start = self.seek_table('loca')
        #self.glyph_pos = []
        glyph_pos_add = self.glyph_pos.append
        if not index_to_loc_format:
            data = self.get_chunk(start, num_glyphs * 2 + 2)
            arr = unpack(">{0}H".format(len(data)/2), data)
            for n in xrange(num_glyphs+1):
                glyph_pos_add(arr[n] * 2)
        elif index_to_loc_format == 1:
            data = self.get_chunk(start, num_glyphs * 4 + 4)
            arr = unpack(">{0}L".format(len(data)/4), data)
            for n in xrange(num_glyphs+1):
                glyph_pos_add(arr[n])
        else:
            raise RuntimeError('Unknown location table format {0}'.format(index_to_loc_format))

    #CMAP Format 4
    def get_CMAP4(self, unicode_cmap_offset, glyph_to_char, char_to_glyph):
        self.max_uni_char = 0
        self.seek(unicode_cmap_offset + 2)
        length = self.read_ushort()
        limit = unicode_cmap_offset + length
        self.skip(2)

        seg_count = self.read_ushort() / 2
        self.skip(6)
        end_count = []
        end_count_add = end_count.append
        for i in xrange(seg_count):
            end_count_add(self.read_ushort())
        self.skip(2)
        start_count = []
        start_count_add = start_count.append
        for i in xrange(seg_count):
            start_count_add(self.read_ushort())
        id_delta = []
        id_delta_add = id_delta.append
        for i in xrange(seg_count):
            id_delta_add(self.read_short()) #???? was unsigned short
        id_range_offset_start = self._pos
        id_range_offset = []
        id_range_offset_add = id_range_offset.append
        for i in xrange(seg_count):
            id_range_offset_add(self.read_ushort())

        for n in xrange(seg_count):
            end_point = end_count[n] + 1
            for unichar in xrange(start_count[n],end_point):
                if not id_range_offset[n]:
                    glyph = (unichar + id_delta[n]) & 0xFFFF
                else:
                    offset = (unichar - start_count[n]) * 2 + id_range_offset[n]
                    offset += id_range_offset_start + 2 * n
                    if offset >= limit:
                        glyph = 0
                    else:
                        glyph = self.get_ushort(offset)
                        if glyph:
                            glyph = (glyph + id_delta[n]) & 0xFFFF
                char_to_glyph[unichar] = glyph
                if unichar < 196608:
                    self.max_uni_char = max(unichar, self.max_uni_char)
                if glyph not in glyph_to_char:
                    glyph_to_char[glyph] = []
                glyph_to_char[glyph].append(unichar)

    #Put the TTF file together
    def end_tt_file(self, stm):
        stm = [stm]
        stm_add = stm.append
        num_tables = len(self.otables)
        search_range = 1
        entry_selector = 0
        while search_range * 2 <= num_tables:
            search_range *= 2
            entry_selector += 1
        search_range *= 16
        range_shift = num_tables * 16 -  search_range

        #Header
        if _TTF_MAC_HEADER:
            stm_add(pack('>LHHHH', 0x74727565, num_tables, search_range, entry_selector, range_shift))   #Mac
        else:
            stm_add(pack('>LHHHH', 0x00010000, num_tables, search_range, entry_selector, range_shift))

        #Table directory
        tables = self.otables
        sorted_tables = sorted(tables)
        offset = 12 + num_tables * 16
        for tag in sorted_tables:
            data = tables[tag]
            if tag == 'head':
                head_start = offset
            stm_add(tag)
            checksum = self.calcChecksum(data)
            stm_add(pack('>HH', checksum[0], checksum[1]))
            stm_add(pack('>LL', offset, len(data)))
            padded_length = (len(data)+3)&~3
            offset += padded_length

        #Table data
        for tag in sorted_tables:
            data = tables[tag] + "\0\0\0"
            stm_add(data[:(len(data)&~3)])

        stm = ''.join(stm)
        checksum = self.calcChecksum(stm)
        checksum = self.sub32((0xB1B0,0xAFBA), checksum)
        chk = pack('>HH', checksum[0], checksum[1])

        stm = self.splice(stm, head_start + 8, chk)
        return  stm
