import { StyleSheet, Platform } from 'react-native';
import { Theme } from '@hw-vmall/vrn-basic-comp';

export default (theme: Theme) =>
  StyleSheet.create({
    vBg: {
      height: Platform.OS === 'web' ? null : 56,
      borderRadius: 16,
      flexDirection: 'row',
      justifyContent: 'space-between',
      overflow: 'hidden',
      paddingBottom: 10,
    },
    vBgPad: {
      height: 56,
      borderRadius: 16,
      flexDirection: 'row',
      justifyContent: 'space-evenly',
      paddingBottom: 10,
      overflow: 'hidden',
    },
    logBlock: {
      alignContent: 'center',
      paddingLeft: 15,
    },
    padBlock: {
      paddingLeft: 0,
      alignItems: 'center',
    },
    shopBlock: {
      paddingLeft: 35,
      alignContent: 'center',
    },
    logoImg: {
      width: 24,
      height: 24,
    },
    leftBlock: {
      flexDirection: 'row',
      justifyContent: 'flex-start',
      alignItems: 'center',
    },
    logoTitle: {
      marginRight: 6,
      alignContent: 'center',
      alignItems: 'center',
      justifyContent: 'center',
      ...theme.T8,
      ...theme.C71,
    },
    textTitle: {
      alignContent: 'center',
      alignItems: 'center',
      justifyContent: 'center',
      ...theme.T8,
      ...theme.C71,
    },
    more: {
      width: 12,
      height: 12,
      ...theme.C24,
    },
    description: {
      width: 140,
      ...theme.T3,
      ...theme.C13,
    },
    shopDescription: {
      width: 112,
      ...theme.T3,
      ...theme.C13,
    },
    splitline: {
      width: 0.5,
      transform: [{ scaleX: 0.5 }],
      backgroundColor: theme.C39.color,
      opacity: theme.C39.opacity,
      height: 24,
    },

    guideBg: {
      alignContent: 'center',
      paddingLeft: 12,
      paddingRight: 12,
      width: '100%',
      flexDirection: 'row',
      justifyContent: 'space-between',
    },

    guideLogoText: {
      height: 19,
      ...theme.T8,
      ...theme.C71,
    },

    guideDescription: {
      ...theme.T3,
      ...theme.C13,
    },

    guideLeftBlock: { maxWidth: '50%' },

    guideRightBlock: {
      height: 28,
      borderRadius: 14,
      backgroundColor: '#312A2A',
    },

    guideButtonText: {
      textAlign: 'center',
      marginTop: 6,
      marginLeft: 12,
      marginRight: 12,
      color: '#FFDBA8',
      ...theme.T4,
    },

    guideButtonOverlong: {
      textAlign: 'center',
      marginTop: 6,
      marginLeft: 6,
      marginRight: 6,
      color: '#FFDBA8',
      ...theme.T4,
    },
  });
