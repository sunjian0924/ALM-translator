#!/usr/bin/env python

"""
Copyright (c) 2009, Daniela Inclezan
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the KRLAB nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY DANIELA INCLEZAN ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL DANIELA INCLEZAN BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS   
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
This software follows a model by Gregory Gelfond.
"""


"""
Copyright (c) 2009, Gregory Gelfond
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the KRLAB nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY GREGORY GELFOND ``AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL GREGORY GELFOND BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS   
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""

import optparse
import sys

from lepl import *

# =====================================
# PREDEFINED STRINGS
# =====================================

NO_INPUT_FILE = 'no input file'


# For the translation to ASP:

GENERAL_AXIOMS = '% General Axioms:\n\n' + \
                 'dom(nodes).\n\n' + \
                 'dom(universe).\n' + \
                 'is_a(universe, nodes).\n\n' + \
                 'dom(actions).\n' + \
                 'is_a(actions, nodes).\n' + \
                 'link(actions, universe).\n\n' + \
                 'dom(booleans).\n' + \
                 'is_a(booleans, nodes).\n' + \
                 'link(booleans, universe).\n\n' + \
                 'instance(X, nodes) :-\n\t' + \
                        'is_a(X, nodes).\n\n' + \
                 'instance(X, Y) :- \n\t' + \
                    'is_a(X, Y), \n\t' + \
                    'dom(X), \n\t' + \
                    'dom(Y), \n\t' + \
                    'is_a(Y, nodes). \n\n' + \
                 'instance(X, Y) :- \n\t' + \
                    'instance(X, Z), \n\t' + \
                    'link(Z, Y), \n\t' + \
                    'dom(X), \n\t' + \
                    'dom(Y), \n\t' + \
                    'dom(Z), \n\t' + \
                    'instance(Y, nodes), \n\t' + \
                    'instance(Z, nodes). \n\n'


# =====================================
# GLOBAL VARS/ STRUCTURES
# =====================================

static = True
basic = True

functions = {}



# =====================================================================

class SortDecl(object):
    """
    Objects of type SortDecl correspond to sort declarations of the 
    language of ALM. Sort declarations are statements of the form:
            s1, ..., sk :: c1, ..., cn
    where:
            s1, ..., sk, c1, ..., cn   -- are sort names
            k >= 1 and n >= 1
    """
    
    def __init__(self, new_sorts, supersorts):
        """
        Creates a new object of the type SortDecl given the list of
        sort names and the supersort.
        """
        global crt_sorts
        crt_sorts = new_sorts
        
        super(SortDecl, self).__init__()
        self.new_sorts = new_sorts
        self.supersorts = supersorts

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        s = ''
        for x in self.new_sorts:
            s = s + 'dom(' + x + ').\nis_a(' + x + ', nodes).\n' 
            for y in self.supersorts:
                s = s + 'link(' + x + ', ' + y + ').\n'
        return s

# =====================================================================

class AttrDecl(object):
    """
    Objects of type AttrDecl correspond to attribute declarations of the 
    language of ALM. Attribute declarations are statements of the form:
            f1, ..., fk : s0 * ... * sn -> s
    where:
            f1, ..., fk  -- are attribute names, k >= 1
            s0, ..., sn -- are sort names with n >= 0
            (If n = 0 then the part "s0 *... * sn -> " is ommitted)
            s -- is a sort name
    """

   
    def __init__(self, attr_names, param_sorts, return_sort):
        """
        Creates a new object of the type AttrDecl given:
        - the list of attributes declared in this attribute declaration,
        - the list of sorts of its parameters (excludig the sort of the first
        implicit parameter, which is the sort to which the attribute
        declaration belongs), and
        - the range of the attribute.
        """
        super(AttrDecl, self).__init__()
        global functions
        
        self.attr_names = attr_names
        self.param_sorts = param_sorts

        if len(crt_sorts) > 1:
            print 'Error: Attributes cannot be specified for multiple sorts at a time.'
        else:
            self.param_sorts.insert(0, crt_sorts[0])
            
        self.return_sort = return_sort

        for attr_name in self.attr_names:
            function_info = []
            function_info.append(static)
            function_info.append(self.param_sorts)
            function_info.append(self.return_sort)
            functions[attr_name] = function_info

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        s = ''
        return s
    
# =====================================================================

class FunctionTypeResetter(object):
    def __init__(self, type_str):
        """
        """
        super(FunctionTypeResetter, self).__init__()

        global static
        global basic
        
        if type_str == 'statics':
            static = True
        elif type_str == 'fluents':
            static = False
        elif type_str == 'basic':
            basic = True
        elif type_str == 'defined':
            basic = False
     
    
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        #TODO
        return ''                       
            
        

# =====================================================================

class FunctionDecl(object):
    """
    Objects of type FunctionDecl correspond to function declarations of the 
    language of ALM. Function declarations are statements of the form:
            f : s1 * ... * sn -> s
    where:
            s1, ..., sn, s   -- are sort names
            n >= 1
    """
    
    def __init__(self, total, function_name, param_sorts, return_sort):
        """
        Creates a new object of the type FunctionDecl given ...
        """
        super(FunctionDecl, self).__init__()
        global functions
        self.total = total
        self.function_name = function_name
        self.param_sorts = param_sorts
        self.return_sort = return_sort
        self.basic = basic
        self.static = static

        function_info = []
        function_info.append(static)
        function_info.append(param_sorts)
        function_info.append(return_sort)
        functions[function_name] = function_info

        #print functions

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        #TODO
        s = '\n'
        s = s + '% CWA for dom_' + self.function_name + '\n\n'
        s = s + '-dom_' + self.function_name + '('
        for i in range(0, len(self.param_sorts)):
            s = s + 'X' + str(i + 1)
            if i < len(self.param_sorts) - 1:
                s = s + ', '
        s = s + ') :-\n\t' 
        s = s + 'not dom_' + self.function_name + '('
        for i in range(0, len(self.param_sorts)):
            s = s + 'X' + str(i + 1)
            if i < len(self.param_sorts) - 1:
                s = s + ', '
        s = s + '),\n\t'
        for i in range(0, len(self.param_sorts)):
            s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
            if i < len(self.param_sorts) - 1:
                s = s + ',\n\t'
        s = s + '.\n\n'


        if self.return_sort == "booleans" :
            s = s + '% Definition of dom_' + self.function_name + '\n\n'
            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + '),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n'

            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + '-' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + '),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n\n'
        else :
            s = s + '% Definition of dom_' + self.function_name + '\n\n'
            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') = X,\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + ',\n\tinstance(X, ' + self.return_sort + ').\n\n'          
        if self.static :
            if self.return_sort == "booleans" :
                s = s + '% Definition of dom_' + self.function_name + '\n\n'
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ') :-\n\t' 
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + '),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + '.\n'

                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ') :-\n\t' 
                s = s + '-' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + '),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + '.\n\n'
            else :
                s = s + '% Definition of dom_' + self.function_name + '\n\n'
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ') :-\n\t' 
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ') = X,\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tinstance(X, ' + self.return_sort + ').\n\n'

        if self.basic and not self.static :
            if self.return_sort == "booleans" :
                s = s + '% Definition of dom_' + self.function_name + '\n\n'
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I) :-\n\t' 
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tstep(I).\n'

                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I) :-\n\t' 
                s = s + '-' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tstep(I).\n\n'
            else :
                s = s + '% Definition of dom_' + self.function_name + '\n\n'
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I) :-\n\t' 
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I) = X,\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tinstance(X, ' + self.return_sort + '),\n\tstep(I).\n\n'

        if not self.static and not self.basic :
            s = s + '% Definition of dom_' + self.function_name + '\n\n'
            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n'
            
        
        if self.basic and self.static :
            s = s + '% CWA for dom_' + self.function_name + '\n\n'
            s = s + '-dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + 'not dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + '),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n\n'

        if not self.basic and self.static :
            s = s + '% CWA for dom_' + self.function_name + '\n\n'
            s = s + '-dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + 'not dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + '),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n\n'

            s = s + '% CWA for ' + self.function_name + '\n\n'
            s = s + '-' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ') :-\n\t' 
            s = s + 'not ' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + '),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + '.\n\n'


        if self.basic and not self.static :
            s = s + '% Inertial Axioms for dom_' + self.function_name + '\n\n'
            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I + 1) :-\n\t' 
            s = s + 'dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I),\n\t'
            s = s + 'not -dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I + 1),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + ',\n\tstep(I).\n\n'

            s = s + '-dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I + 1) :-\n\t' 
            s = s + '-dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I),\n\t'
            s = s + 'not dom_' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I + 1),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + ',\n\tstep(I).\n\n'

            s = s + '% Inertial Axioms for ' + self.function_name + '\n\n'
            if self.return_sort == "booleans" :
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1) :-\n\t' 
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1),\n\t'
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I),\n\t'
                s = s + 'not -' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tstep(I).\n'

                s = s + '-' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1) :-\n\t' 
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1),\n\t'
                s = s + '-' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I),\n\t'
                s = s + 'not ' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tstep(I).\n\n'
            else :
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1) = X :-\n\t' 
                s = s + 'dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1),\n\t'
                s = s + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I) = X,\n\t'
                s = s + 'not ' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I + 1) != X,\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tinstance(X, ' + self.return_sort +  '),\n\t'
                s = s + 'step(I).\n\n'

        if not self.static and not self.basic :
            s = s + '% CWA for ' + self.function_name + '\n\n'
            s = s + '-' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I) :-\n\t' 
            s = s + 'not ' + self.function_name + '('
            for i in range(0, len(self.param_sorts)):
                s = s + 'X' + str(i + 1)
                if i < len(self.param_sorts) - 1:
                    s = s + ', '
            s = s + ', I),\n\t'
            for i in range(0, len(self.param_sorts)):
                s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                if i < len(self.param_sorts) - 1:
                    s = s + ',\n\t'
            s = s + ',\n\tstep(I).\n\n'
        if hasattr(self, 'total') : 
            if self.static :
                s = s + '% ' + self.function_name + ' is a total function\n'
                s = s + ':- -dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + '),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + '.\n\n'
            else :
                s = s + '% ' + self.function_name + ' is a total function\n\n'
                s = s + ':- -dom_' + self.function_name + '('
                for i in range(0, len(self.param_sorts)):
                    s = s + 'X' + str(i + 1)
                    if i < len(self.param_sorts) - 1:
                        s = s + ', '
                s = s + ', I),\n\t'
                for i in range(0, len(self.param_sorts)):
                    s = s + 'instance' + '(' + 'X' + str(i+1) + ', ' + self.param_sorts[i] + ')'
                    if i < len(self.param_sorts) - 1:
                        s = s + ',\n\t'
                s = s + ',\n\tstep(I).\n\n'

        return s

# =====================================================================

class DynamicCausalLaw(object):
	"""
	Objects of type DynamicCausalLaw correspond to dynamic causal laws of
	the language of ALM. Dynamic causal laws are statements of the form:
		occurs(a) causes l if p
	where:
		a    -- is a variable or a constant
		l    -- is an basic fluent literal
		p    -- is a set of literals
	"""
	
	def __init__(self, occ, head, body):
		"""
		Creates a new object of the type DynamicCausalLaw given: 
		occ - the "occurs" expression represented as a list [occurs, a]
		head - the head literal represented as a list
		body - the body literals represented as a list
		"""
		super(DynamicCausalLaw, self).__init__()
		self.occ = occ
		self.head = head
		self.body = body
		self.variables = get_vars([occ, head, body])
		
		print self.occ
		print self.head
		print self.body
		print self.variables
		print functions


        def logic_program_form(self):
            """
            Returns the translation into ASP
            """
            #TODO
            # determine step variable
            a_set = set()
            step = ''
            if 'I' in self.variables:
                i = 1
                while 'I' + str(i) not in self.variables :
                    i += 1
                step = 'I' + str(i)
            else :
                step = 'I'
            s = ''
            # assemble head
            s = s + self.head[0] + '('
            for i in range(0, len(self.head[1])) :
                s = s + self.head[1][i]
                if i < len(self.head[1]) - 1:
                    s = s + ', '
            s = s + ', ' + step + ' + 1) '
            for i in range(2, len(self.head)) : 
                s = s + self.head[i]
                if i < len(self.head) - 1:
                    s = s + ' '
            s = s + ' :-\n\t'

            functionName = ''
            if self.head[0][0] == '-' :
                functionName = self.head[0][1:]
            else :
                functionName = self.head[0]
            if functionName in functions :
                for i in range(0, len(self.head[1])) :
                    temps = "instance(" + self.head[1][i] + ", " + functions[functionName][1][i] + ")"   
                    a_set.add(temps)

            # occ
            temps = ''
            temps = temps + self.occ[0] + '('
            for i in range(1, len(self.occ)) :
                temps = temps + self.occ[i]
                if i < len(self.occ) - 1:
                    temps = temps + ', '
            temps = temps + ', ' + step + ')'
            a_set.add(temps)
            for i in range(1, len(self.occ)) :
                a_set.add('instance(' + self.occ[i] + ', actions)') 

            # body
            for j in range(0, len(self.body)):
                # literal is arithmetic expression
                if isinstance(self.body[j][1], str):
                    temps = ''
                    for i in range(0, len(self.body[j])):
                        temps = temps + self.body[j][i]
                        if i < len(self.body[j]) - 1:
                            temps = temps + ' '
                    a_set.add(temps)
                else:
                    if self.body[j][0][0] == '-' :
                        functionName = self.body[j][0][1:]
                    else :
                        functionName = self.body[j][0]
                    if functionName in functions:
                        for i in range(0, len(self.body[j][1])):
                            temps = "instance(" + self.body[j][1][i] + ", " + functions[functionName][1][i] + ")"   
                            a_set.add(temps)
                        if len(temps) > 3:
                            temps = "instance(" + self.body[j][3] + ", " + functions[functionName][2] + ")"   
                            a_set.add(temps)
                        # static
                        if functions[functionName][0]:  
                            temps = ''
                            temps = temps + self.body[j][0] + '('
                            for i in range(0, len(self.body[j][1])):
                                temps = temps + self.body[j][1][i]
                                if i < len(self.body[j][1]) - 1:
                                    temps = temps + ', '
                            temps = temps + ') '
                            for i in range(2, len(self.body[j])):
                                temps = temps + self.body[j][i]
                                if i < len(self.body[j]) - 1:
                                    temps = temps + ' '
                            a_set.add(temps)
                        else :
                            # fluent
                            temps = ''
                            temps = temps + self.body[j][0] + '('
                            for i in range(0, len(self.body[j][1])):
                                temps = temps + self.body[j][1][i]
                                if i < len(self.body[j][1]) - 1:
                                    temps = temps + ', '
                            temps = temps + ', ' + step + ') '
                            for i in range(2, len(self.body[j])):
                                temps = temps + self.body[j][i]
                                if i < len(self.body[j]) - 1:
                                    temps = temps + ' '
                            a_set.add(temps)
                    else:
                        temps = ''
                        temps = temps + self.body[j][0] + '('
                        for i in range(0, len(self.body[j][1])):
                            temps = temps + self.body[j][1][i]
                            if i < len(self.body[j][1]) - 1:
                                temps = temps + ', '
                        temps = temps + ')'
                        for i in range(2, len(self.body[j])):
                            temps = temps + self.body[j][i]
                            if i < len(self.body[j]) - 1:
                                temps = temps + ' '
                        a_set.add(temps)


            i = 0
            for item in a_set:
                s = s + item
                if i < len(a_set) - 1:
                    s = s + ',\n\t'
                i = i + 1
            s = s + '.\n\n'
            return s

	    
# =====================================================================

class SystemDescription(object):
    """
    Objects of type SystemDescription correspond to system descriptions 
    of the language of ALM. System descriptions are statements of the 
    form:
            system description <name>
                theory <name1>
                    [module]+
                structure <name2>
                     <structure description>
    where:
            <name>, <name1>, <name2>   -- are constants
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type SystemDescription given the        
        system description name.
        """
        super(SystemDescription, self).__init__()
        self.name = name
        
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% ASP{f} Translation of System Description ' + self.name + '\n\n'   

# =====================================================================

class Theory(object):
    """
    Objects of type Theory correspond to theories of system descriptions
    of the language of ALM. Theories are statements of the form:
            theory <name>
                [module]+
    where:
            <name>   -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Theory given the        
        theory name.
        """
        super(Theory, self).__init__()
        self.name = name

    def logic_program_form(self):
        """
        Returns the translation into ASP{f}
        """
        return '% -------------------------------------\n' +\
               '% Theory ' + self.name + '\n' +\
               '% -------------------------------------\n\n' +\
               GENERAL_AXIOMS

# =====================================================================

class Structure(object):
    """
    Objects of type Structure correspond to structures of the 
    language of ALM. The structure is a statement of the form:
            structure <name>
                <structure description>
    where:
            <name>    -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Structure given the        
        structure name.
        """
        super(Structure, self).__init__()
        self.name = name

        
    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% -------------------------------------\n' +\
               '% Structure ' + self.name + '\n' +\
               '% -------------------------------------\n\n'

# =====================================================================

class Module(object):
    """
    Objects of type Module correspond to system descriptions of the 
    language of ALM. Modules are declared as:
            module <name>
    where:
            <name>    -- is a constant
    """
    
    def __init__(self, name):
        """
        Creates a new object of the type Module given the module name.       
        """
        super(Module, self).__init__()
        self.name = name
        

    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return '% -------------------------------------\n' +\
               '% Module ' + self.name + '\n\n'
    
# =====================================================================

class SortDeclarations(object):
    """
    Objects of type SortDeclarations correspond to statements of the form:
            sort declarations
    """
    
    def __init__(self, something):
        """
        """    
        super(SortDeclarations, self).__init__()


    def logic_program_form(self):
        """
        Returns the translation into ASP
        """
        return "\n% Sort Declarations\n\n"


# =====================================================================
# ALM LANGUAGE GRAMMAR
# =====================================================================

# =====================================
# BASIC TOKEN TYPES
# =====================================
 
CONSTANT  = Token('[a-z][_a-zA-Z0-9]*')
VARIABLE  = Token('[A-Z][_a-zA-Z0-9]*')

NUMBER    = Token(Integer())

COMMA     = Token(',') 
SUBSORT   = Token('::')
COLON     = Token(':')
TIMES     = Token('\*')
RARROW    = Token('\->')

LPAREN    = Token('\(')
RPAREN    = Token('\)')
EQ        = Token('=')
NEQ       = Token('!=')

ARITH_OP  = Or(
              Token('\+'),
              Token('\-'),
              Token('\*'),
              Token('/')
            )

# =====================================
# SORT DECLARATIONS
# =====================================

CT_LIST = CONSTANT & ZeroOrMore(~COMMA & CONSTANT) > list

ATTR_DOMAIN = Optional(CONSTANT & ZeroOrMore(~TIMES & CONSTANT) & ~RARROW) > list

ATTR_DECL = CT_LIST & ~COLON & ATTR_DOMAIN & CONSTANT > args(AttrDecl)

SORT_ATTRS = ~Token('attributes') & OneOrMore(ATTR_DECL)

SORT_DECL_HEAD = CT_LIST & ~SUBSORT & CT_LIST > args(SortDecl)

SORT_DECL = SORT_DECL_HEAD & Optional(SORT_ATTRS)

SORT_DECLARATIONS_HEADER = ~Token('sort declarations')

SORT_DECLARATIONS = SORT_DECLARATIONS_HEADER & OneOrMore(SORT_DECL)

# =====================================
# FUNCTION DECLARATIONS
# =====================================

TOTAL_PARTIAL = Optional(Token('total')) > set

FUNC_DOMAIN = CONSTANT & ZeroOrMore(~TIMES & CONSTANT) & ~RARROW > list

FUNC_DECL = TOTAL_PARTIAL & CONSTANT & ~COLON & FUNC_DOMAIN & CONSTANT > args(FunctionDecl)

FUNC_SECTION = OneOrMore(FUNC_DECL)

FUNC_SECTION_HEADER = Or(
        Token('basic'),
        Token('defined')
    ) > args(FunctionTypeResetter)

FUNC_BODY = OneOrMore(FUNC_SECTION_HEADER & FUNC_SECTION)

FUNC_HEADER = Or(
        Token('statics'),
        Token('fluents')
    ) > args(FunctionTypeResetter)
    
FUNCTION_DECLARATIONS_BODY = OneOrMore(FUNC_HEADER & FUNC_BODY)

FUNCTION_DECLARATIONS_HEADER = ~Token('function declarations')

FUNCTION_DECLARATIONS = FUNCTION_DECLARATIONS_HEADER & FUNCTION_DECLARATIONS_BODY

# =====================================
# DYNAMIC_CAUSAL_LAW
# =====================================

CV = Or(CONSTANT, VARIABLE)

CVN = Or(CV, NUMBER)

DCL_OCC = Token('occurs') & ~LPAREN & CV & ~RPAREN > list


LIT_NAME = Optional(Token('\-')) & CONSTANT > ''.join

PARAMS = Optional(~LPAREN & CVN & ZeroOrMore(~COMMA & CVN) & ~RPAREN) > list

BOOL_BASIC_LIT = LIT_NAME & PARAMS > list


NON_BOOL_BASIC_LIT = CONSTANT & PARAMS & Or(EQ, NEQ) & CVN > list

BASIC_LIT = Or(BOOL_BASIC_LIT, NON_BOOL_BASIC_LIT)


ARITH_LIT = CVN & ARITH_OP & CVN & Or(EQ, NEQ) & CVN > list


DCL_LIT = Or(BASIC_LIT, ARITH_LIT)

DCL_BODY = Optional(~Token('if') & DCL_LIT & ZeroOrMore(~COMMA & DCL_LIT)) > list

DYNAMIC_CAUSAL_LAW = DCL_OCC & ~Token('causes') & BASIC_LIT & DCL_BODY & ~Token('\.') > args(DynamicCausalLaw)

# =====================================
# MODULE
# =====================================

#AXIOM = Or(
#			DYNAMIC_CAUSAL_LAW,
#			STATE_CONSTRAINT,
#			EXECUTABILITY_CONDITION
#			)
			
AXIOM = DYNAMIC_CAUSAL_LAW		

AXIOMS = ~Token('axioms') & OneOrMore(AXIOM)

MODULE_BODY = SORT_DECLARATIONS & FUNCTION_DECLARATIONS & Optional(AXIOMS)

MODULE_HEADER = ~Token('module') & CONSTANT > args(Module)

MODULE_SECTION = MODULE_HEADER & MODULE_BODY

# =====================================
# SYSTEM DESCRIPTION
# =====================================

THEORY_HEADER = ~Token('theory') & CONSTANT > args(Theory)

THEORY_SECTION = THEORY_HEADER & OneOrMore(MODULE_SECTION)


STRUCTURE_HEADER = ~Token('structure') & CONSTANT > args(Structure)

STRUCTURE_SECTION = STRUCTURE_HEADER


SYSTEM_DESCRIPTION_HEADER = ~Token('system description') & CONSTANT \
                            > args(SystemDescription)

EOF = ~Eof()

SYSTEM_DESCRIPTION = SYSTEM_DESCRIPTION_HEADER & THEORY_SECTION & STRUCTURE_SECTION \
                     & ~EOF


# =====================================================================
# DRIVER AND UTILITY FUNCTIONS
# =====================================================================

# =====================================
# UTILITY FUNCTIONS
# =====================================

def rewrite_lp(f_lp, statement):
    """
    Given an object representation a statement of the language ALM,
    prints the logic program form of the statement to file f_lp
    """
    f_lp.write(statement.logic_program_form())

def flatten_list(l):
	result = []
	for x in l:
		if hasattr(x, '__iter__'):
			aux = flatten_list(x)
			result.extend(aux)
		else:
			result.append(x)
	return result
	
def is_variable(text):
    return text[0].isupper()

def is_constant(text):
    return text[0].islower()
	
def get_vars(l):
	result = []
	for x in flatten_list(l):
		if is_variable(x) :
			result.append(x)
	return list(set(result))

# =====================================
# PROGRAM DRIVER
# =====================================


def main():
    if len(sys.argv) != 2:
        print 'You need to write "ALMtranslator.py" and the name of the \
               input file'
    else:
        try:
            source = open(sys.argv[1], 'r')
  
            representation = SYSTEM_DESCRIPTION.parse_file(source)
            if representation != None:
                print 'The syntax analysis of the input file "' + \
                       sys.argv[1] + '" was successful'

                lp_output_file = sys.argv[1].rpartition('.')[0] + '.lp'
                f_lp = open(lp_output_file, 'w')
                list_lp = []

                for i in range (0,len(representation)):
                    list_lp.append(f_lp)
                map(rewrite_lp, list_lp, representation)
                f_lp.close()

            else:
                print 'The input file "' + sys.argv[1] + \
                          '" contains syntax errors!!!'

            print "\n",    
            source.close()
        except IOError:
            print "Unable to open the file: " + options.filename
   
if __name__ == "__main__":
    main()






