import { StyleSheet, Dimensions } from 'react-native';
import { PublicFont, Theme, CommonUtils, PlatformUtils, FONT_MUTIPLE } from '@hw-vmall/vrn-basic-comp';
const SCALE_SIZE = FONT_MUTIPLE.FONT_LEVEL_FOUR;
export default (theme: Theme, isMember?: boolean) => {
  return StyleSheet.create({
    cardbgdefa: {
      height: 60,
      borderRadius: 16,
      flexDirection: 'row',
      justifyContent: 'center',
      paddingBottom: 12,
      paddingTop: 12,
    },
    cardbgb: {
      flexDirection: 'row',
      alignItems: 'center',
      justifyContent: 'space-evenly',
      minWidth: '33.3%',
      backgroundColor: 'rgba(255,255,255,0.96)',
      borderRadius: 16,
      paddingVertical: 12,
    },
    harmonyCard: {
      flexDirection: 'row',
      alignItems: 'center',
      justifyContent: 'space-evenly',
      paddingHorizontal: 8,
      paddingVertical: 12,
      backgroundColor: 'rgba(255, 255, 255, 0.96)',
      borderRadius: 16,
    },
    bigPadHView: {
      height: 122,
    },
    cardbgbPad: {
      flexDirection: 'row',
      justifyContent: 'space-evenly',
      alignItems: 'center',
      minWidth: '33.3%',
      backgroundColor: 'rgba(255,255,255,0.96)',
      borderRadius: 16,
      paddingVertical: 12,
    },
    itemdefaul: {
      flex: 1,
      flexDirection: 'column',
      alignItems: 'center',
      textAlign: 'center',
      justifyContent: 'center', // space-evenly PAd
    },
    assterIcon: {
      width: 40,
      height: 40,
      marginBottom: 4,
    },
    assterTitle: {
      color: 'rgba(24,36,49,1)',
      fontSize: 12,
      fontWeight: '400',
    },
    itemPadDefaul: {
      flexGrow: 1,
      flexDirection: 'row',
      textAlign: 'center',
      justifyContent: 'center', // space-evenly PAd
    },
    itemChildwap: {
      flexDirection: 'column',
      alignItems: 'center',
      justifyContent: 'center',
    },
    itemChild: {
      maxWidth: PlatformUtils.isPc(Dimensions.get('window').width) ? '100%' : '50%',
      flexGrow: 1,
      flexDirection: 'column',
      justifyContent: 'center',
    },
    wordsText: {
      ...theme.T3,
      fontSize: CommonUtils.getScaleSize(12, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(16, SCALE_SIZE),
      color: 'rgba(0,0,0,.9)',
      fontWeight: '400',
    },
    wordsTextTwo: {
      ...theme.T3,
      fontSize: CommonUtils.getScaleSize(12, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(16, SCALE_SIZE),
      color: 'rgba(0,0,0,.9)',
      fontWeight: '400',
    },
    wordsTextPc: {
      fontFamily: PublicFont.fontFamilyBase,
      marginLeft: 8,
      ...theme.T10,
      ...theme.C15,
    },
    wordsTextPcTwo: {
      fontFamily: PublicFont.fontFamilyBase,
      ...theme.T2,
      ...theme.C15,
    },
    numText: {
      fontFamily: PublicFont.fontFamilyBase,
      ...theme.T8,
      ...theme.C17,
      fontSize: CommonUtils.getScaleSize(10, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(14, SCALE_SIZE),
      opacity: 0.4,
      color: '#000000',
      fontWeight: '400',
      marginTop: 2,
      marginBottom: 4,
    },
    numTextNo: {
      ...theme.T8,
      ...theme.C17,
      fontSize: CommonUtils.getScaleSize(10, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(14, SCALE_SIZE),
      opacity: 0.4,
      color: '#000000',
      fontWeight: '400',
      marginTop: 2,
      marginBottom: 4,
    },
    numSymbolPc: {
      textAlign:'center',
      fontFamily: PublicFont.fontFamilyBase,
      ...theme.T13,
      ...theme.C11,
    },
    numTextPc: {
      textAlign:'center',
      fontFamily: PublicFont.fontFamilyBase,
      ...theme.T13,
      ...theme.C11,
    },
    splitline: {
      width: 1,
      transform: [{ scaleX: 0.5 }],
      backgroundColor: isMember ? theme.C51.color : theme.C13.color,
      opacity: isMember ? 0.2 : 0.1,
      marginTop: 6,
    },
    bonusContainer: {
      flexDirection: 'row',
      justifyContent: 'center',
      alignItems: 'center',
      marginTop: 9,
    },
  });
};
