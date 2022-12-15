from Fonctions.converter import *

def isHeureDepartDansHohaireBrancardier(heure, brancardier):
    """"
    Methode qui verifie si une heure se trouve dans les horaires du brancardier
    \n"L'heure est elle comprise dans les horaires du brancardiers" 
    """
    heureAVerifier = heure_to_intSecondes(heure)
    horaireBrancardier_borneMinMat= heure_to_intSecondes(brancardier["heure_debut_travail"])
    horaireBrancardier_borneMaxMat= heure_to_intSecondes(brancardier["heure_fin_matin"])
    horaireBrancardier_borneMinAp= heure_to_intSecondes(brancardier["heure_debut_apres_midi"])
    horaireBrancardier_borneMaxAp= heure_to_intSecondes(brancardier["heure_fin_travail"])
    if (heureAVerifier>horaireBrancardier_borneMinMat and heureAVerifier<horaireBrancardier_borneMaxMat) or (heureAVerifier>horaireBrancardier_borneMinAp and heureAVerifier<horaireBrancardier_borneMaxAp) :
        return True
    else :     
        return False


def checkHeureDepartETHeureDispo(heure, brancardier):
    """
    Methode qui verifie si une heure est superieure à l'heure de disponibilite du brancardier, autrement dit "le brancardier sera-t-il disponible à cette heure ?" 
    """
    if heure_to_intSecondes(heure)> heure_to_intSecondes(brancardier["heure_dispo"]):
        return True
    else: 
        return False