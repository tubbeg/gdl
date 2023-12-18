(ns gdl.protocols) ; TODO not only protocols, also Context ...
; TODO call context ?
; other protocols somewhere else like screen or disposable ?

(defrecord Context [])

(defprotocol Disposable
  (dispose [_]))

(defprotocol TrueTypeFontGenerator
  (generate-ttf [_ {:keys [file size]}]))
