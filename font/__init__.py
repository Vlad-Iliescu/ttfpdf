__author__ = 'Vlad'

#//============================================================+
#// File name   : makefont.php
#// Begin       : 2004-12-31
#// Last Update : 2010-12-03
#// Version     : 1.2.007
#// License     : GNU LGPL (http://www.gnu.org/copyleft/lesser.html)
#//     ----------------------------------------------------------------------------
#//     Copyright (C) 2008-2010  Nicola Asuni - Tecnick.com S.r.l.
#//
#// This file is part of TCPDF software library.
#//
#// TCPDF is free software: you can redistribute it and/or modify it
#// under the terms of the GNU Lesser General Public License as
#// published by the Free Software Foundation, either version 3 of the
#// License, or (at your option) any later version.
#//
#// TCPDF is distributed in the hope that it will be useful, but
#// WITHOUT ANY WARRANTY; without even the implied warranty of
#// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
#// See the GNU Lesser General Public License for more details.
#//
#// You should have received a copy of the GNU Lesser General Public License
#// along with TCPDF.  If not, see <http://www.gnu.org/licenses/>.
#//
#// See LICENSE.TXT file for more information.
#//  ----------------------------------------------------------------------------
#//
#// Description : Utility to generate font definition files fot TCPDF
#//
#// Authors: Nicola Asuni, Olivier Plathey, Steven Wittens
#//
#// (c) Copyright:
#//               Nicola Asuni
#//               Tecnick.com S.r.l.
#//               Via della Pace, 11
#//               09044 Quartucciu (CA)
#//               ITALY
#//               www.tecnick.com
#//               info@tecnick.com
#//============================================================+
#
import os
import zlib
import re
from struct import unpack

def substr(s, start, length=None):
    """ Gets a substring from a string"""
    if length is None:
        length = len(s) - start
    return s[start:start+length]

class MakeFont():
    def __init__(self):
        self.widths = {}
        self.compress = True

    def get_metrics(self, fontfile, fmfile, embedded=True, enc='cp1252', patch = ()):
        """Generate a font definition file"""
        if not os.path.exists(fontfile):
            raise RuntimeError('File not found: '+fontfile)
        if not os.path.exists(fmfile):
            raise RuntimeError('File not found: '+fmfile)
        if not patch:
            patch = dict()
        cid_to_gidmap = ''
        cmap = {}
        diff = ''
        dw = 0 #default width
        ff_ext = fontfile.split('.')[-1]
        fm_ext = fmfile.split('.')[-1]
        if fm_ext == 'afm':
            if ff_ext == 'ttf' or ff_ext == 'otf':
                type = 'TrueType'
            elif ff_ext == 'pfb':
                type = 'Type1'
            else:
                raise RuntimeError('Unrecognized font file extension: '+ff_ext)
            if enc:
                cmap = self.read_map(enc)
                for cc, gn in patch.iteritems():
                    cmap[cc] = gn
            fm, cmap = self.read_afm(fmfile, cmap)
            if '.notdef' in self.widths:
                dw = self.widths['.notdef']
            if enc:
                diff = self.make_font_encoding(cmap)
            fd = self.make_font_descriptor(fm, bool(cmap))
        elif fm_ext == 'ufm':
            enc = ''
            if ff_ext == 'ttf' or ff_ext == 'otf':
                type = 'TrueTypeUnicode'
            else:
                raise RuntimeError('Not a TrueType font: '+ff_ext)
            fm, cid_to_gidmap = self.read_ufm(fmfile)
            dw = fm['MissingWidth']
            fd = self.make_font_descriptor(fm, False)
        else:
            raise RuntimeError('Unknown extension'+fm_ext)
        #Start generation
        s = [
            "type = '{0}'\n".format(type),
            "name = '{0}'\n".format(fm['FontName']),
            "desc = {0}\n".format(fd)
        ]
        if 'UnderlinePosition' not in fm:
            fm['UnderlinePosition'] = -100
        if 'UnderlineThickness' not in fm:
            fm['UnderlineThickness'] = 50
        s.append("up = {0}\n".format(fm['UnderlinePosition']))
        s.append("up = {0}\n".format(fm['UnderlineThickness']))
        if dw <= 0:
            if 'Widths' in fm and 32 in fm['Widths'] and fm['Widths'][32] > 0:
                dw = fm['Widths'][32]
            else:
                dw = 600
        s.append("dw = {0}\n".format(dw))
        w = self.make_width_array(fm)
        s.append("cw = {0}\n".format(w))
        s.append("enc = '{0}'\n".format(enc))
        s.append("diff = '{0}'\n".format(diff))
        basename = ''.join(os.path.basename(fmfile).split('.')[:-1])
        if embedded:
            #Embedded font
            if type == 'TrueType' or type == 'TrueTypeUnicode':
                self.check_ttf(fontfile)
            f = open(fontfile, 'rb')
            if not f:
                raise RuntimeError('Unable to open file: '+fontfile)
            file = f.read()
            f.close()
            if type == 'Type1':
                #Find first two sections and discard third one
                header = (ord(file[0]) == 128)
                if header:
                    file = file[6:]
                pos = file.find('eexec')
                if pos < 0:
                    raise RuntimeError('Font file does not seem to be valid Type1')
                size1 = pos + 6
                if header and (ord(file[size1]) == 128):
                    #Strip second binary header
                    file = file[:size1] + file[size1+6:]
                pos = file.find('00000000')
                if pos < 0:
                    raise RuntimeError('Font file does not seem to be valid Type1')
                size2 = pos - size1
                file = file[:size1+size2]
            basename = basename.lower()
            if self.compress:
                cmp = basename + '.z'
                self.save_to_file(cmp, zlib.compress(file, 9), 'b')
                s.append("file = '{0}'\n".format(cmp))
                if cid_to_gidmap:
                    cmp = basename + '.ctg.z'
                    self.save_to_file(cmp, zlib.compress(file, 9), 'b')
                    s.append("ctg = '{0}'\n".format(cmp))
            else:
                s.append("file = '{0}'\n".format(os.path.basename(fontfile)))
                if cid_to_gidmap:
                    cmp = basename + '.ctg'
                    f = open(cmp, 'wb')
                    f.write(cid_to_gidmap)
                    f.close()
                    s.append("ctg = '{0}'\n".format(cmp))
            if type == 'Type1':
                s.append("size1 = {0}\n".format(size1))
                s.append("size2 = {0}\n".format(size2))
            else:
                s.append("originalsize = {0}\n".format(os.path.getsize(fontfile)))
        else:
            #Not embedded font
            s.append("file = ''\n")
        self.save_to_file(basename + '.py', ''.join(s))

    def read_map(self, enc):
        file = os.path.join('enc', enc.lower()+'.map')
        if not os.path.exists(file):
            raise RuntimeError('Encoding not found: '+enc)
        a = open(file)
        cc2gn = {}
        for l in self._filereader(a):
            if l[0] == '!':
                e = re.split('[ \\t]+', l.rstrip())
                cc = int(e[0][1:] , 16)
                gn = e[2]
                cc2gn[cc] = gn

        for i in xrange(255):
            if i not in cc2gn:
                cc2gn[i] = '.notdef'

        return cc2gn

    def read_afm(self, file, cmap):
        """Read a font metric file"""
        a = open(file)
        if not a:
            raise RuntimeError('File not found')
        fm = {}
        fix = {'Edot':'Edotaccent','edot':'edotaccent','Idot':'Idotaccent','Zdot':'Zdotaccent','zdot':'zdotaccent',
               'Odblacute':'Ohungarumlaut','odblacute':'ohungarumlaut','Udblacute':'Uhungarumlaut','udblacute':'uhungarumlaut',
               'Gcedilla':'Gcommaaccent','gcedilla':'gcommaaccent','Kcedilla':'Kcommaaccent','kcedilla':'kcommaaccent',
               'Lcedilla':'Lcommaaccent','lcedilla':'lcommaaccent','Ncedilla':'Ncommaaccent','ncedilla':'ncommaaccent',
               'Rcedilla':'Rcommaaccent','rcedilla':'rcommaaccent','Scedilla':'Scommaaccent','scedilla':'scommaaccent',
               'Tcedilla':'Tcommaaccent','tcedilla':'tcommaaccent','Dslash':'Dcroat','dslash':'dcroat','Dmacron':'Dcroat','dmacron':'dcroat',
               'combininggraveaccent':'gravecomb','combininghookabove':'hookabovecomb','combiningtildeaccent':'tildecomb',
               'combiningacuteaccent':'acutecomb','combiningdotbelow':'dotbelowcomb','dongsign':'dong'}
        for l in self._filereader(a):
            e = l.rstrip(' \n').split(' ')
            if len(e) < 2:
                continue
            code = e[0]
            param = e[1]
            if code == 'C':
                #Character metrics
                cc = int(e[1])
                w = e[4]
                gn = e[7]
                if gn[-4:] == '20AC':
                    gn = 'Euro'
                if gn in fix:
                    #Fix incorrect glyph name
                    for c,n in cmap.iteritems():
                        if n == fix[gn]:
                            cmap[c] = gn
                if not cmap:
                    #Symbolic font: use built-in encoding
                    self.widths[cc] = int(w)
                else:
                    self.widths[gn] = int(w)
                    if gn == 'X':
                        fm['CapXHeight'] = e[13]
                if gn == '.notdef':
                    fm['MissingWidth'] = w
            elif code == 'FontName':
                fm['FontName'] = param
            elif code == 'Weight':
                fm['Weight'] = param
            elif code == 'ItalicAngle':
                fm['ItalicAngle'] = float(param)
            elif code == 'Ascender':
                fm['Ascender'] = int(param)
            elif code == 'Descender':
                fm['Descender'] = int(param)
            elif code == 'UnderlineThickness':
                fm['UnderlineThickness'] = int(param)
            elif code == 'UnderlinePosition':
                fm['UnderlinePosition'] = int(param)
            elif code == 'IsFixedPitch':
                fm['IsFixedPitch'] = bool(param == 'true')
            elif code == 'FontBBox':
                fm['FontBBox'] = [e[1], e[2], e[3], e[4]]
            elif code == 'CapHeight':
                fm['CapHeight'] = int(param)
            elif code == 'StdVW':
                fm['StdVW'] = int(param)
        if 'FontName' not in fm:
            raise RuntimeError('FontName not found.')
        if cmap:
            if '.notdef' not in self.widths:
                self.widths['.notdef'] = 600
            if 'Delta' not in self.widths and 'increment' in self.widths:
                self.widths['Delta'] = self.widths['increment']
            #Order widths according to map
            for i in xrange(255):
                if cmap[i] not in self.widths:
                    self.widths[i] = self.widths['.notdef']
                else:
                    self.widths[i] = self.widths[cmap[i]]
        fm['Widths'] = self.widths
        return fm, cmap

    def make_font_encoding(self, cmap):
        """Build differences from reference encoding"""
        ref = self.read_map('cp1252')
        s = []
        add = s.append
        last = 0
        for i in xrange(32,256):
            if cmap[i] != ref[i]:
                if i != last + 1:
                    add('{0} '.format(i))
                last = i
                add('/{0} '.format(cmap[i]))
        return ''.join(s).rstrip(' ')

    def make_font_descriptor(self, fm, symbolic):
        #Ascent
        asc = fm['Ascender'] if 'Ascender' in fm else 1000
        fd = {'Ascent': asc}
        #Descent
        desc = fm['Descender'] if 'Descender' in fm else -200
        fd['Descender'] = desc
        #CapHeight
        if 'CapHeight' in fm:
            ch = fm['CapHeight']
        elif 'CapXHeight' in fm:
            ch = fm['CapXHeight']
        else:
            ch = asc
        fd['CapHeight'] = ch
        #Flags
        flags = 0
        if 'IsFixedPitch' in fm and fm['IsFixedPitch']:
            flags += 1 << 0
        if symbolic:
            flags += 1 << 2
        if not symbolic:
            flags += 1 << 5
        if 'ItalicAngle' in fm and fm['ItalicAngle'] != 0:
            flags += 1 << 6
        fd['Flags'] = flags
        #FontBBox
        if 'FontBBox' in fm:
            fbb = fm['FontBBox']
        else:
            fbb = [0, desc - 100, 1000, asc + 100]
        fm['FontBBox'] = fbb
        #ItalicAngle
        ia = fm['ItalicAngle'] if 'ItalicAngle' in fm else 0
        fd['ItalicAngle'] = ia
        #StemV
        if 'StdVW' in fm:
            stemv = fm['StdVW']
        elif 'Weight' in fm and re.search('(bold|black)', fm['Weight'], re.I):
            stemv = 120
        else:
            stemv = 70
        fd['StemV'] = stemv
        #MissingWidth
        if 'MissingWidth' in fm:
            fd['MissingWidth'] = fm['MissingWidth']
        return fd

    def read_ufm(self, file):
        #Prepare empty CIDToGIDMap
        cid_to_gidmap = ["\x00" for _i in xrange(256*256*2)]
        #Read a font metric file
        a = open(file)
        if not a:
            raise RuntimeError('File not found.')
        fm = {}
        for l in self._filereader(a):
            e = l.rstrip(' ').split(' ')
            if len(e) < 2:
                continue
            code = e[0]
            param = e[1]
            gn = 0
            if code == 'U':
                #U 827 ; WX 0 ; N squaresubnosp ; G 675 ;
                #Character metrics
                cc = int(e[1])
                if cc != -1:
                    gn = e[7]
                    w = e[4]
                    glyph = e[10]
                    self.widths[cc] = w
                    if cc == ord('X'):
                        fm['CapXHeight'] = e[13]
                    #Set GID
                    if (cc >= 0) and (cc < 0xFFFF) and glyph:
                        cid_to_gidmap[(cc * 2)] = chr(glyph >> 8)
                        cid_to_gidmap[((cc * 2) + 1)] = chr(glyph & 0xFF)
                if gn and gn == '.notdef' and 'MissingWidth' not in fm:
                    fm['MissingWidth'] = w
            elif code == 'FontName':
                fm['FontName'] = param
            elif code == 'Weight':
                fm['Weight'] = param
            elif code == 'ItalicAngle':
                fm['ItalicAngle'] = float(param)
            elif code == 'Ascender':
                fm['Ascender'] = int(param)
            elif code == 'Descender':
                fm['Descender'] = int(param)
            elif code == 'UnderlineThickness':
                fm['UnderlineThickness'] = int(param)
            elif code == 'UnderlinePosition':
                fm['UnderlinePosition'] = int(param)
            elif code == 'IsFixedPitch':
                fm['IsFixedPitch'] = bool(param == 'true')
            elif code == 'FontBBox':
                fm['FontBBox'] = [e[1], e[2], e[3], e[4]]
            elif code == 'CapHeight':
                fm['CapHeight'] = int(param)
            elif code == 'StdVW':
                fm['StdVW'] = int(param)
        if 'MissingWidth' not in fm:
            fm['MissingWidth'] = 600
        if 'FontName' not in fm:
            raise RuntimeError('FontName not found')
        fm['Widths'] = self.widths
        return fm, ''.join(cid_to_gidmap)

    def make_width_array(self, fm):
        """Make character width array"""
        s = ['{']
        add = s.append
        for i in xrange(255):
            add(' chr({0}):{1},'.format(i, fm['Widths'][i]))
            if i and not i % 8:
                add("\n\t\t")
        add('}')
        return ''.join(s)

    def check_ttf(self, file):
        """Check if font license allows embedding"""
        f = open(file, 'rb')
        if not f:
            raise RuntimeError('Can\'t open file: {0}'.format(file))
        #Extract number of tables
        f.seek(4, os.SEEK_CUR)
        nb = self.read_short(f)
        f.seek(6, os.SEEK_CUR)
        #Seek OS/2 table
        found = False
        for i in xrange(nb):
            if f.read(4) == 'OS/2':
                found = True
                break
            f.seek(12, os.SEEK_CUR)
        if not found:
            f.close()
            return
        f.seek(4, os.SEEK_CUR)
        offset = self.read_long(f)
        f.seek(offset, os.SEEK_SET)
        #Extract fsType flags
        f.seek(8, os.SEEK_CUR)
        fs_type = self.read_short(f)
        rl = (fs_type & 0x02) != 0
        pp = (fs_type & 0x04) != 0
        e = (fs_type & 0x08) != 0
        f.close()
        if rl and not pp and not e:
            raise RuntimeWarning('Font license does not allow embedding')

    def save_to_file(self, file, s, mode='t'):
        f = open(file, 'w'+mode)
        if not f:
            raise RuntimeError('Can\'t write to file: {0}'.format(file))
        f.write(s)
        f.close()

    def read_short(self, f):
        a = unpack('>H', f.read(2))
        return a[0]

    def read_long(self, f):
        a = unpack('>L', f.read(4))
        return a[0]

    def _filereader(self, file):
        while True:
            line = file.readline()
            if not line:
                break
            yield line

if __name__ == "__main__":
    fmake = MakeFont()
    fmake.get_metrics('UniversCEMedium.ttf', 'univers.afm')