def heure_to_intSecondes(heure) :
    """
    Methode de conversion d'une heure au format "HH'h'MM" en nombre de secondes, pour faciliter les calculs de temps
    """
    h = heure[0:2]
    m = heure[3:5]
    h_int = int(h)
    m_int = int(m)
    tps = m_int*60 + h_int*3600
    return tps


def intSecondes_to_heure(intSecondes) :
    """
    Methode de conversion d'un nombre de secondes en heure au format "HH'h'MM", pour récupérer heure suite à un calcul
    """
    h=intSecondes//3600
    m=int((intSecondes/60)%60)
    if m <10:
        m="0"+str(m)
    if h <10:
        h="0"+str(h)
    tps= str(h) +"h"+str(m)
    return tps