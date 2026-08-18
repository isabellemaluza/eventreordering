theory JSHTMLSyntax
imports JSMemoryModel
begin

datatype html_attr =
    Attr string string
  | AttrOnClick expr
  | AttrOnMouseOver expr

datatype html_node =
    HtmlText string
  | HtmlElement string "html_attr list" "html_node list"

value "HtmlText ''Ola''"

value "HtmlElement ''p''
         [Attr ''id'' ''msg'', Attr ''color'' ''yellow'']
         [HtmlText ''Ola'']"

value "HtmlElement ''button''
         [AttrOnClick
            (ESeq
               (ECall (EVar ''alert'') [EConst (VString ''Ola'')])
               (ECall (EVar ''changeColor'')
                      [EVar ''this'', EConst (VString ''blue'')]))]
         [HtmlText ''Clique'']"

end
